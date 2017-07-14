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

/* Suppress accelerator's `main`. */
#define MAIN accelerator_main
#include "accelerator.c"

#include <CUnit/Basic.h>
#include <dirent.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static char *xstrdup(const char *s) {
    char *p = strdup(s);
    CU_ASSERT_PTR_NOT_NULL_FATAL(p);
    return p;
}

static char *xmkdtemp(void) {
    char *dir = xstrdup("/tmp/tmp.XXXXXX");
    char *result = mkdtemp(dir);
    CU_ASSERT_PTR_NOT_NULL_FATAL(result);
    return dir;
}

#define xaprintf(args...) \
    ({ \
        char *_p; \
        int _r = asprintf(&_p, args); \
        CU_ASSERT_FATAL(_r != -1); \
        _p; \
    })

static int rmtree(const char *path) {
    struct stat st;
    if (stat(path, &st) != 0)
        return -1;

    if (S_ISDIR(st.st_mode)) {
        DIR *d = opendir(path);
        if (d == NULL)
            return -1;

        while (true) {
            struct dirent entry, *result;
            if (readdir_r(d, &entry, &result) != 0)
                return -1;

            if (result == NULL)
                break;

            if (!strcmp(entry.d_name, ".") || !strcmp(entry.d_name, ".."))
                continue;

            char *child = xaprintf("%s/%s", path, entry.d_name);
            if (rmtree(child) != 0)
                return -1;
            free(child);
        }

        closedir(d);

        return rmdir(path);
    } else {
        return unlink(path);
    }
}

void *xrealloc(void *ptr, size_t size) {
    void *p = realloc(ptr, size);
    CU_ASSERT_PTR_NOT_NULL_FATAL(p);
    return p;
}

static char *run(const char *command) {
    char *buffer = NULL;
    size_t len = 0;
    size_t sz = 0;

    FILE *p = popen(command, "r");
    CU_ASSERT_PTR_NOT_NULL_FATAL(p);

    while (true) {
        if (len == sz) {
            buffer = xrealloc(buffer, sz + 1024);
            sz += 1024;
        }

        size_t consumed = fread(buffer + len, 1, sz - len, p);
        if (consumed == 0) {
            CU_ASSERT_TRUE_FATAL(feof(p));
            buffer[len] = '\0';
            break;
        }
        len += consumed;
    }

    pclose(p);
    return buffer;
}

/* The common case of copying a file. */
static void copy_file_normal(void) {
    static const char *CONTENT = "hello world\n";
    char *srcdir = xmkdtemp();
    char *src = xaprintf("%s/foo", srcdir);
    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fputs(CONTENT, f);
    fclose(f);

    char *dstdir = xmkdtemp();
    char *dst = xaprintf("%s/bar", dstdir);

    int result = copy_file(src, dst);
    free(src);
    CU_ASSERT(result == 0);

    /* Check the file was correctly copied. */
    if (result == 0) {
        f = fopen(dst, "r");
        CU_ASSERT_PTR_NOT_NULL_FATAL(f);
        char buffer[1024];
        char *res = fgets(buffer, sizeof(buffer), f);
        fclose(f);
        CU_ASSERT_PTR_NOT_NULL_FATAL(res);
        CU_ASSERT_STRING_EQUAL(buffer, CONTENT);
    }

    free(dst);

    /* Check that no extra directory entries were created. */
    DIR *d = opendir(srcdir);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, "..") ||
                  !strcmp(entry->d_name, "foo"));
    }
    closedir(d);
    d = opendir(dstdir);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, "..") ||
                  !strcmp(entry->d_name, "bar"));
    }
    closedir(d);

    rmtree(srcdir);
    free(srcdir);
    rmtree(dstdir);
    free(dstdir);
}

/* Ensure copying of a non-existent file always fails. */
static void copy_file_no_source(void) {
    char *tmp = xmkdtemp();
    char *src = xaprintf("%s/foo", tmp);
    char *dst = xaprintf("%s/bar", tmp);

    /* Check that copying of the non-existent file fails. */
    int result = copy_file(src, dst);
    free(src);
    free(dst);
    CU_ASSERT_FATAL(result != 0);

    /* Check that no files were created in the directory. */
    DIR *d = opendir(tmp);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, ".."));
    }
    closedir(d);

    rmtree(tmp);
    free(tmp);
}

/* Copy a file to an output directory that does not exist. */
static void copy_file_no_destination(void) {
    static const char *CONTENT = "hello world\n";
    char *tmp = xmkdtemp();

    char *src = xaprintf("%s/foo", tmp);
    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fputs(CONTENT, f);
    fclose(f);

    char *dst = xaprintf("%s/bar/baz", tmp);

    int result = copy_file(src, dst);
    free(dst);
    CU_ASSERT_FATAL(result != 0);

    /* Check that no files were created in the directory. */
    DIR *d = opendir(tmp);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, "..") ||
                  !strcmp(entry->d_name, "foo"));
    }
    closedir(d);

    /* Ensure we did not modify the source file. */
    f = fopen(src, "r");
    free(src);
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    char buffer[1024];
    char *res = fgets(buffer, sizeof(buffer), f);
    fclose(f);
    CU_ASSERT_PTR_NOT_NULL_FATAL(res);
    CU_ASSERT_STRING_EQUAL(buffer, CONTENT);

    rmtree(tmp);
    free(tmp);
}

/* The common case of moving a file. */
static void move_file_normal(void) {
    static const char *CONTENT = "hello world\n";
    char *srcdir = xmkdtemp();
    char *src = xaprintf("%s/foo", srcdir);
    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fputs(CONTENT, f);
    fclose(f);

    char *dstdir = xmkdtemp();
    char *dst = xaprintf("%s/bar", dstdir);

    int result = move_file(src, dst);
    free(src);
    CU_ASSERT(result == 0);

    /* Check the file was correctly copied. */
    if (result == 0) {
        f = fopen(dst, "r");
        CU_ASSERT_PTR_NOT_NULL_FATAL(f);
        char buffer[1024];
        char *res = fgets(buffer, sizeof(buffer), f);
        fclose(f);
        CU_ASSERT_PTR_NOT_NULL_FATAL(res);
        CU_ASSERT_STRING_EQUAL(buffer, CONTENT);
    }

    free(dst);

    /* Check that no extra directory entries were created. */
    DIR *d = opendir(srcdir);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, ".."));
    }
    closedir(d);
    d = opendir(dstdir);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, "..") ||
                  !strcmp(entry->d_name, "bar"));
    }
    closedir(d);

    rmtree(srcdir);
    free(srcdir);
    rmtree(dstdir);
    free(dstdir);
}

/* Ensure moving a non-existent file always fails. */
static void move_file_no_source(void) {
    char *tmp = xmkdtemp();
    char *src = xaprintf("%s/foo", tmp);
    char *dst = xaprintf("%s/bar", tmp);

    /* Check that moving of the non-existent file fails. */
    int result = move_file(src, dst);
    free(src);
    free(dst);
    CU_ASSERT_FATAL(result != 0);

    /* Check that no files were created in the directory. */
    DIR *d = opendir(tmp);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, ".."));
    }
    closedir(d);

    rmtree(tmp);
    free(tmp);
}

/* Move a file to an output directory that does not exist. */
static void move_file_no_destination(void) {
    static const char *CONTENT = "hello world\n";
    char *tmp = xmkdtemp();

    char *src = xaprintf("%s/foo", tmp);
    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fputs(CONTENT, f);
    fclose(f);

    char *dst = xaprintf("%s/bar/baz", tmp);

    int result = move_file(src, dst);
    free(dst);
    CU_ASSERT_FATAL(result != 0);

    /* Check that no files were created in the directory and the original
     * source remains.
     */
    DIR *d = opendir(tmp);
    CU_ASSERT_PTR_NOT_NULL_FATAL(d);
    struct dirent *entry;
    while ((entry = readdir(d)) != NULL) {
        CU_ASSERT(!strcmp(entry->d_name, ".") ||
                  !strcmp(entry->d_name, "..") ||
                  !strcmp(entry->d_name, "foo"));
    }
    closedir(d);

    /* Ensure we did not modify the source file. */
    f = fopen(src, "r");
    free(src);
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    char buffer[1024];
    char *res = fgets(buffer, sizeof(buffer), f);
    fclose(f);
    CU_ASSERT_PTR_NOT_NULL_FATAL(res);
    CU_ASSERT_STRING_EQUAL(buffer, CONTENT);

    rmtree(tmp);
    free(tmp);
}

static void make_temp_normal(void) {
    char *tmp = make_temp();
    CU_ASSERT_PTR_NOT_NULL_FATAL(tmp);

    /* Ensure the file is blank. */
    FILE *f = fopen(tmp, "r");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    char buffer[1024];
    char *data = fgets(buffer, sizeof(buffer), f);
    CU_ASSERT_PTR_NULL(data);
    fclose(f);

    rmtree(tmp);
}

static void is_hex_empty(void) {
    CU_ASSERT_TRUE(is_hex((unsigned char*)""));
}

static void is_hex_single_char_exhaust(void) {
    unsigned char str[2] = {0, '\0'};
    for (unsigned char c = 1; ; c++) {
        str[0] = c;
        bool hex = is_hex(str);
        if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') ||
                (c >= 'A' && c <= 'F')) {
            CU_ASSERT_TRUE(hex);
        } else {
            CU_ASSERT_FALSE(hex);
        }
        if (c == UCHAR_MAX)
            break;
    }
}

static void hash_file_normal(void) {
    char *tmp = xmkdtemp();
    char *src = xaprintf("%s/foo", tmp);

    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fputs("hello world\n", f);
    fclose(f);

    const char *hash = hash_file(src);
    CU_ASSERT_PTR_NOT_NULL_FATAL(hash);
    CU_ASSERT_FATAL(strlen(hash) == 64);

    char *cmd = xaprintf("sha256sum %s", src);
    free(src);
    char *output = run(cmd);
    free(cmd);

    CU_ASSERT(strncmp(hash, output, strlen(hash)) == 0);
    free(output);

    rmtree(tmp);
    free(tmp);
}

static void hash_file_empty(void) {
    char *tmp = xmkdtemp();
    char *src = xaprintf("%s/foo", tmp);

    FILE *f = fopen(src, "w");
    CU_ASSERT_PTR_NOT_NULL_FATAL(f);
    fclose(f);

    const char *hash = hash_file(src);
    CU_ASSERT_PTR_NOT_NULL_FATAL(hash);
    CU_ASSERT_FATAL(strlen(hash) == 64);

    char *cmd = xaprintf("sha256sum %s", src);
    free(src);
    char *output = run(cmd);
    free(cmd);

    CU_ASSERT(strncmp(hash, output, strlen(hash)) == 0);
    free(output);

    rmtree(tmp);
    free(tmp);
}

static void hash_file_missing(void) {
    char *tmp = xmkdtemp();
    char *src = xaprintf("%s/foo", tmp);

    const char *hash = hash_file(src);
    free(src);
    CU_ASSERT_PTR_NULL_FATAL(hash);

    rmtree(tmp);
    free(tmp);
}

int main(void) {
    CU_ErrorCode err = 0;

    if (CU_initialize_registry() != CUE_SUCCESS) {
        err = CU_get_error();
        fprintf(stderr, "failed to initialise CUnit\n");
        goto fail0;
    }

    CU_pSuite suite = CU_add_suite("accelerator", NULL, NULL);
    if (suite == NULL) {
        err = CU_get_error();
        fprintf(stderr, "failed to add suite\n");
        goto fail1;
    }

    if ((CU_add_test(suite, "is_hex(\"\")", is_hex_empty) == NULL) ||
        (CU_add_test(suite, "is_hex(r\".\")", is_hex_single_char_exhaust) == NULL) ||
        (CU_add_test(suite, "copy_file(foo, bar)", copy_file_normal) == NULL) ||
        (CU_add_test(suite, "copy_file(<non-existent>, ...)", copy_file_no_source) == NULL) ||
        (CU_add_test(suite, "copy_file(foo, <non-existent dir>/baz)", copy_file_no_destination) == NULL) ||
        (CU_add_test(suite, "move_file(foo, bar)", move_file_normal) == NULL) ||
        (CU_add_test(suite, "move_file(<non-existent>, ...)", move_file_no_source) == NULL) ||
        (CU_add_test(suite, "move_file(foo, <non-existent dir>/baz)", move_file_no_destination) == NULL) ||
        (CU_add_test(suite, "make_temp()", make_temp_normal) == NULL) ||
        (CU_add_test(suite, "hash_file(<file>)", hash_file_normal) == NULL) ||
        (CU_add_test(suite, "hash_file(<empty file>)", hash_file_empty) == NULL) ||
        (CU_add_test(suite, "hash_file(<missing file>)", hash_file_missing) == NULL)) {
        err = CU_get_error();
        fprintf(stderr, "failed to add tests\n");
        goto fail1;
    }

    CU_basic_set_mode(CU_BRM_VERBOSE);
    CU_basic_run_tests();
    err = CU_get_number_of_tests_failed();

fail1: CU_cleanup_registry();
fail0: return err;
}
