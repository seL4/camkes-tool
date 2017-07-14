/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/* CAmkES accelerator.
 *
 * It was observed that an unavoidable overhead in the previous design of the
 * CAmkES code generator, even when retrieving previously cached results, was
 * the start up of the Python VM. By reading cached results in a native process
 * and then determining if we still need to run the code generator, this
 * overhead can be avoided. To that end, this program implements a level A
 * cache reader without relying on Python.
 *
 * ----
 *
 * Dependencies:
 *  - Linux
 *  - The CMake build system tool (cmake)
 *  - The Ninja build system tool (ninja-build)
 *  - OpenSSL (libssl-dev)
 *  - SQLite 3 (libsqlite3-dev)
 *  - CAmkES
 *  - xxd (`man xxd`)
 *
 * ----
 *
 * The CAmkES code generator can write to two compilation caches during
 * execution, the level A cache and the level B cache. The level A cache's
 * backing store is language independent. In particular, it doesn't store any
 * Python data structures; only strings. This was a deliberate design decision
 * to allow non-Python programs to read cache entries.
 *
 * With caching enabled, the code generator first checks the level A cache. On
 * a cache miss, it then checks the level B cache. On a cache miss here, it now
 * has to actually generate code. On a cache hit at either level, it exits
 * immediately with the returned result.
 *
 * Serving results directly from the level A cache is significantly faster than
 * code generation. However, in a large build it is still noticeably slower
 * than, e.g., C code compilation. To remedy this, it was suggested that we
 * move the check of the level A cache outside Python itself. This avoids many
 * costly operations involved in setting up a Python execution environment.
 *
 * This program implements the described check of the level A cache and nothing
 * more. In particular, it simply exits with failure on a cache miss. The idea
 * is that you run this and use its exit status to determine whether you need
 * to run the code generator. Though similar tools like Ccache will actually
 * execute your compiler on a cache miss, we have greater control over how the
 * code generator is invoked and so such tricks are an unnecessary complexity.
 *
 * Note that the code generator itself still contains a check of the level A
 * cache. It is assumed that you may not have the accelerator enabled but still
 * want to get some benefit from cached results.
 */

#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/limits.h>
#include <openssl/sha.h>
#include "select_inputs.h" /* generated */
#include "select_output.h" /* generated */
#include <sqlite3.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/sendfile.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include "version.h" /* generated */

#ifdef DEBUG
    #define ERR(args...) \
        do { \
            fprintf(stderr, "camkes-accelerator %s:", VERSION); \
            fprintf(stderr, args); \
            fprintf(stderr, "\n"); \
        } while (0)
#else
    #define ERR(args...) /* nothing */
#endif

/* Compiler hint that a condition is most likely false. This allows the
 * compiler to layout code in such a way that not taking this branch is faster.
 * This is only used below in the case of unexpected errors, not in conditions
 * that indicate a cache miss. The rationale for this is that it can make the
 * branch drammatically more expensive if it is taken.
 */
#define unlikely(cond) __builtin_expect((cond), 0)

/* Chunk size used for allocation at various points. */
static const unsigned CHUNK_SIZE = 1024;

static int copy_file(const char *source, const char *destination) {
    assert(source != NULL);
    assert(destination != NULL);

    int ret = -1;

    int in = open(source, O_RDONLY);
    if (unlikely(in == -1)) {
        ERR("failed to open %s for reading", source);
        goto fail1;
    }

    struct stat st;
    if (unlikely(fstat(in, &st) == -1)) {
        ERR("failed to stat %s", source);
        goto fail2;
    }

    int out = open(destination, O_WRONLY|O_CREAT|O_TRUNC, st.st_mode);
    if (unlikely(out == -1)) {
        ERR("failed to open %s for writing", destination);
        goto fail2;
    }

    if (unlikely(sendfile(out, in, NULL, st.st_size) == -1)) {
        ERR("failed to copy %s to %s", source, destination);
        goto fail3;
    }

    ret = 0;

fail3: close(out);
fail2: close(in);
fail1: return ret;
}

static int move_file(const char *source, const char *destination) {
    int result = rename(source, destination);
    if (result == -1 && errno == EXDEV) {
        /* The operation crosses file system boundaries. Emulate it with copy
         * then delete.
         */
        result = copy_file(source, destination);
        if (result == 0)
            result = unlink(source);
    }
    return result;
}

static char *make_temp(void) {
    char *path = strdup("/tmp/tmp.XXXXXX"); /* mkstemp needs this writable */
    if (unlikely(path == NULL))
        return NULL;
    int fd = mkstemp(path);
    if (unlikely(fd == -1)) {
        free(path);                                                             /* goanna: suppress=MEM-free-no-alloc */
        return NULL;
    }
    close(fd);
    return path;
}

/* Returns true if a byte string only contains hex values. */
static bool is_hex(const unsigned char *s) __attribute__((unused));
static bool is_hex(const unsigned char *s) {
    while (*s != '\0') {
        switch (*s) {
            case '0' ... '9':
            case 'a' ... 'f':
            case 'A' ... 'F':
                break;
            default:
                return false;
        }
        s++;
    }
    return true;
}

static int write_dependency(FILE *f, const char *path) {
    return fprintf(f, " \\\n  %s", path);
}

#define str_eq(s1, s2_literal) \
    (strncmp((s1), s2_literal, sizeof("" s2_literal "")) == 0)

static void digest_to_hex_digest(const unsigned char *digest, char *hexdigest) {
    for (unsigned i = 0; i < SHA256_DIGEST_LENGTH; i++) {
        sprintf(&hexdigest[i * 2], "%02x", digest[i]);
    }
}

static void hash_string(const char *string, char *hexdigest) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256((const unsigned char*)string, strlen(string), digest);
    digest_to_hex_digest(digest, hexdigest);
}

/* Calculate the SHA256 hex digest of a file. Returns NULL on failure and a
 * pointer to a static string on success. Note that by implication it is NOT
 * THREAD SAFE.
 */
static const char *hash_file(const char *path) {
    const char *result = NULL;
    static char hexdigest[SHA256_DIGEST_LENGTH * 2 + 1];

    int fd = open(path, O_RDONLY);
    if (fd == -1) {
        ERR("failed to open %s", path);
        goto fail1;
    }

    /* Measure the size of the file. */
    struct stat st;
    if (unlikely(fstat(fd, &st) == -1)) {
        ERR("failed to stat %s", path);
        goto fail2;
    }
    size_t size = (size_t)st.st_size;

    void *addr = NULL;
    if (size > 0) {
        /* Mmap the file. Note that we use some flags to optimise for the
         * sequential read `SHA256` is about to perform, and we ignore failure
         * of `madvise` as this is just part of the optimisation.
         */
        addr = mmap(NULL, size, PROT_READ, MAP_PRIVATE|MAP_POPULATE, fd, 0);
        if (unlikely(addr == MAP_FAILED)) {
            ERR("failed to mmap %s", path);
            goto fail2;
        }
        madvise(addr, size, MADV_SEQUENTIAL|MADV_WILLNEED);
    }

    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256(addr, size, digest);
    digest_to_hex_digest(digest, hexdigest);
    result = hexdigest;

    if (size > 0)
        munmap(addr, size);

fail2: close(fd);
fail1: return result;
}

/* The CAmkES default to --cache-dir. */
static char *default_cache_prefix(void) {
    static char dir[PATH_MAX];
    char *home = getenv("HOME");
    if (home == NULL) {
        fprintf(stderr, "HOME environment variable not set\n");
        return NULL;
    }
    sprintf(dir, "%s/.camkes/cache", home);
    return dir;
}

/* Return the actual directory used by the level A cache. We need to mimic the
 * logic CAmkES uses to locate this cache.
 */
static char *get_cache_dir(char *prefix) {
    if (prefix == NULL) {
        prefix = default_cache_prefix();
        if (prefix == NULL)
            return NULL;
    }
    char *dir;
    if (unlikely(asprintf(&dir, "%s/%s/cachea", prefix, VERSION) == -1)) {
        fprintf(stderr, "failed to resolve cache directory\n");
        return NULL;
    }
    return dir;
}

/* Wrap sqlite3_prepare_v2. It does not have a particularly pleasant calling
 * convention.
 */
static sqlite3_stmt *_sqlite_prepare(sqlite3 *db, const char *query,
        size_t len) {
    sqlite3_stmt *stmt;
    if (unlikely(sqlite3_prepare_v2(db, query, len, &stmt, NULL)
            != SQLITE_OK)) {
        ERR("failed to prepare SQL statement \"%s\"", query);
        return NULL;
    }
    return stmt;
}
#define sqlite_prepare(db, query) \
    _sqlite_prepare((db), ((const char*)query), query##_len)

/* Find an output under the given parameters in the opened database. Returns
 * the id of the output if found, or -1 otherwise. The SHA256 of the output
 * itself is returned in the 'output' parameter.
 */
static int find_output(char **output, sqlite3 *db, char *args, char *cwd) {
    int id = -1;

    /* The query below needs to *exactly* match the one used for level A cache
     * lookups by CAmkES.
     */
    sqlite3_stmt *stmt = sqlite_prepare(db, select_output_sql);
    if (unlikely(stmt == NULL))
        goto end;

    if (unlikely(sqlite3_bind_text(stmt, 1, args, -1, SQLITE_STATIC)
            != SQLITE_OK)) {
        ERR("failed to bind args to SQL query");
        goto end;
    }

    if (unlikely(sqlite3_bind_text(stmt, 2, cwd, -1, SQLITE_STATIC)
            != SQLITE_OK)) {
        ERR("failed to bind cwd to SQL query");
        goto end;
    }

    if (sqlite3_step(stmt) != SQLITE_ROW) {
        /* Cache miss, database timeout, etc. */
        ERR("cache miss (anticipated scenario)");
        goto end;
    }

    assert(sqlite3_column_count(stmt) == 2);

    assert(sqlite3_column_type(stmt, 1) == SQLITE_TEXT);
    const unsigned char *_sha256 = sqlite3_column_text(stmt, 1);
    assert(is_hex(_sha256));
    const char *sha256 = (const char*)_sha256;
    if (unlikely(sha256 == NULL)) {
        ERR("failed to retrieve sha256 column");
        goto end;
    }
    /* Duplicate this as SQLite reclaims the backing memory for 'sha256'. */
    *output = strdup(sha256);
    if (unlikely(*output == NULL)) {
        ERR("out of memory while duplicating sha256");
        goto end;
    }

    assert(sqlite3_column_type(stmt, 0) == SQLITE_INTEGER);
    id = sqlite3_column_int(stmt, 0);
    if (unlikely(id == 0)) {
        ERR("failed to retrieve id column");
        id = -1;
        free(*output);
    }

end:
    sqlite3_finalize(stmt);
    return id;
}

/* Check whether a set of inputs in the level A cache database are still valid.
 * That is, do the hashes of their current on-disk content match the hashes in
 * the database? If not, the cache entry is stale and cannot be used. Returns
 * true if the entry is still valid.
 */
static bool valid_inputs(sqlite3 *db, int id, FILE *deps) {
    int result = false;

    /* Again, this query needs to *exactly* match the one used by CAmkES in
     * level A cache lookups.
     */
    sqlite3_stmt *stmt = sqlite_prepare(db, select_inputs_sql);
    if (unlikely(stmt == NULL))
        goto fail;

    if (unlikely(sqlite3_bind_int(stmt, 1, id) != SQLITE_OK)) {
        ERR("failed to bind id to SQL query");
        goto fail;
    }

    while (true) {
        int r = sqlite3_step(stmt);
        if (r == SQLITE_DONE) {
            /* Checked all inputs. */
            break;
        } else if (unlikely(r != SQLITE_ROW)) {
            ERR("unexpected error from sqlite3_step");
            goto fail;
        }

        assert(r == SQLITE_ROW);

        assert(sqlite3_column_type(stmt, 0) == SQLITE_TEXT);
        const char *path = (const char*)sqlite3_column_text(stmt, 0);
        if (unlikely(path == NULL)) {
            ERR("failed to retrieve path column");
            goto fail;
        }

        assert(sqlite3_column_type(stmt, 1) == SQLITE_TEXT);
        const unsigned char *_sha256 = sqlite3_column_text(stmt, 1);
        assert(is_hex(_sha256));
        const char *sha256 = (const char*)_sha256;
        if (unlikely(sha256 == NULL)) {
            ERR("failed to retrieve sha256 column");
            goto fail;
        }

        const char *current_sha256 = hash_file(path);
        if (current_sha256 == NULL) {
            /* Can't hash current file. Maybe it doesn't exist. */
            ERR("failed to hash %s", path);
            goto fail;
        }
        if (strcmp(sha256, current_sha256) != 0) {
            /* Hashes don't match. Stale entry. */
            ERR("mismatched hash of %s (%s != %s)", path, sha256,
                current_sha256);
            goto fail;
        }

        if (deps != NULL)
            write_dependency(deps, path);
    }
    result = true;

fail:
    sqlite3_finalize(stmt);
    return result;
}

/* Find the cache entry for a given set of parameters. Returns NULL if there is
 * no valid matching entry.
 */
static char *find_entry(char *cache_dir, char *args, char *cwd, FILE *deps) {
    sqlite3 *db;

    char *ret = NULL;

    char args_hexdigest[SHA256_DIGEST_LENGTH * 2 + 1];
    assert(args != NULL);
    hash_string(args, args_hexdigest);

    char cwd_hexdigest[SHA256_DIGEST_LENGTH * 2 + 1];
    assert(cwd != NULL);
    hash_string(cwd, cwd_hexdigest);

    char *path;
    if (unlikely(asprintf(&path, "%s/dbs/%s/%s/cache.db", cache_dir,
            args_hexdigest, cwd_hexdigest) == -1))
        goto fail1;

    if (sqlite3_open_v2(path, &db, SQLITE_OPEN_READONLY, NULL) != 0) {
        ERR("failed to open database %s\n", path);
        goto fail2;
    }

    int res __attribute__((unused)) = sqlite3_exec(db, "begin transaction;",
        NULL, NULL, NULL);
    /* This should always succeed because beginning a transaction does nothing
     * until you perform the first read or write.
     */
    assert(res == SQLITE_OK && "failed to begin transaction");

    char *output;
    int id = find_output(&output, db, args, cwd);
    if (id == -1)
        goto fail3;

    if (valid_inputs(db, id, deps)) {
        ret = output;
    } else {
        free(output);                                                           /* goanna: suppress=MEM-free-no-alloc */
    }

fail3: sqlite3_exec(db,
        /* Whether we rollback or commit this transaction is irrelevant as we
         * only performed reads, but we may as well be semantically consistent.
         */
        ret == NULL ? "rollback transaction" : "commit transaction",
        NULL, NULL, NULL);
fail2: free(path);                                                              /* goanna: suppress=MEM-free-no-alloc */
       sqlite3_close(db);
fail1: return ret;
}

/* Allow the unit tests to suppress `main`. */
#ifndef MAIN
    #define MAIN main
#endif

int MAIN(int argc, char **argv) {

    assert(argc >= 1);
    if (unlikely(argc == 1)) {
        fprintf(stderr, "no arguments provided\n");
        return -1;
    }

    char *cache_prefix = NULL;
    char *output = NULL;
    char *deps_file = NULL;

    /* Collect all the command line arguments in a \n-separated string. This is
     * the manner in which CAmkES stores command-line arguments in the level A
     * cache.
     */
    size_t args_sz = CHUNK_SIZE;
    char *args = malloc(sizeof(char) * args_sz);
    if (unlikely(args == NULL)) {
        fputs("out of memory\n", stderr);
        return -1;
    }
    size_t args_len = 0;
    args[0] = '\0';
    for (unsigned i = 1; i < (unsigned)argc; i++) {
        size_t len = strlen(argv[i]);

        /* Parse command line arguments. We could do this with getopt, but
         * since we need to iterate over the arguments and would like to accept
         * arbitrary future arguments, just do it inline here.
         */
        if (str_eq(argv[i], "--help")) {
            fprintf(stderr, "CAmkES cache accelerator\n"
                            "  usage: %s arguments...\n", argv[0]);
            free(args);
            return -1;
        } else if (str_eq(argv[i], "--version")) {
            fprintf(stderr, "CAmkES cache accelerator %s\n", VERSION);
            free(args);
            return 0;
        } else if (str_eq(argv[i], "--cache-dir") &&
                   i + 1 < (unsigned)argc) {
            cache_prefix = argv[i + 1];
        } else if ((str_eq(argv[i], "--outfile") ||
                    str_eq(argv[i], "-O")) &&                                   /* goanna: suppress=ARR-inv-index-ptr-pos */
                   i + 1 < (unsigned)argc) {
            output = argv[i + 1];
            /* Skip --outfile and its parameter. */
            i++;
            continue;
        } else if ((str_eq(argv[i], "--makefile-dependencies") ||
                    str_eq(argv[i], "-MD")) &&
                   i + 1 < (unsigned)argc) {
            deps_file = argv[i + 1];
        }

        /* Do we need to expand the argument buffer? */
        if (args_len + 1 + len + 1 > args_sz) {
            args_sz += CHUNK_SIZE;
            char *args_ = realloc(args, args_sz);                               /* goanna: suppress=MEM-leak-alias */
            if (unlikely(args_ == NULL)) {
                fputs("out of memory\n", stderr);
                free(args);
                return -1;
            }
            args = args_;
        }

        /* Separate arguments with new line. */
        if (args_len > 0) {
            args[args_len] = '\n';
            args_len++;
        }

        strncpy(&args[args_len], argv[i], len);
        args_len += len;
    }
    args[args_len] = '\0';

    if (unlikely(output == NULL)) {
        fprintf(stderr, "no output path provided\n");
        free(args);
        return -1;
    }

    char cwd[PATH_MAX];
    if (unlikely(getcwd(cwd, PATH_MAX) == NULL)) {
        fprintf(stderr, "failed to retrieve current directory\n");
        free(args);
        return -1;
    }

    /* At this point, we have the inputs we need. Now time to locate and open
     * the cache.
     */

    char *cache_dir = get_cache_dir(cache_prefix);
    assert(cache_dir != NULL);

    /* If we are supposed to write Make dependencies, set up a temporary file
     * we can write these into. On success we'll move this to the intended
     * location.
     */
    const char *tmp_deps_file = NULL;
    FILE *deps = NULL;
    if (deps_file != NULL) {
        tmp_deps_file = make_temp();
        if (unlikely(tmp_deps_file == NULL)) {
            fputs("failed to create temporary file\n", stderr);
            free(cache_dir);
            free(args);
            return -1;
        }
        deps = fopen(tmp_deps_file, "w");
        if (unlikely(deps == NULL)) {
            fputs("failed to open temporary file\n", stderr);
            free((void*)tmp_deps_file);
            free(cache_dir);
            free(args);
            return -1;
        }
        fprintf(deps, "%s: ", output);
    }

    char *entry = find_entry(cache_dir, args, cwd, deps);
    free(args);
    /* We no longer need the dependency file handle. */
    if (deps != NULL) {
        fprintf(deps, "\n");
        fclose(deps);
    }
    if (entry == NULL) {
        /* Cache miss. */
        if (tmp_deps_file != NULL) {
            unlink(tmp_deps_file);
            free((void*)tmp_deps_file);                                         /* goanna: suppress=MEM-free-no-alloc */
        }
        free(cache_dir);
        return -1;
    }

    /* Move the dependency file into its intended location. */
    if (deps_file != NULL) {
        assert(tmp_deps_file != NULL);
        int result = move_file(tmp_deps_file, deps_file);
        free((void*)tmp_deps_file);                                             /* goanna: suppress=MEM-free-no-alloc */
        if (unlikely(result != 0)) {
            fputs("failed to create dependency file\n", stderr);
            free(entry);
            free(cache_dir);
            return -1;
        }
    }

    /* Find the path to the entry. */
    char *source;
    int result = asprintf(&source, "%s/data/%s", cache_dir, entry);
    free(entry);
    free(cache_dir);
    if (unlikely(result == -1)) {
        fprintf(stderr, "failed to construct cache entry path\n");
        return -1;
    }

    result = copy_file(source, output);
    free(source);                                                               /* goanna: suppress=MEM-free-no-alloc */
    return result;
}
