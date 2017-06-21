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

/* Minimal SQLite linter.
 *
 * This program takes input consisting of a file containing an SQLite
 * statement. It returns 0 if the file contains a valid statement or -2 if the
 * file contains lexical errors. In the case of error, it will also print out a
 * textual description of the error.
 *
 * To build:
 *
 *     cc -W -Wall -Wextra -Werror -o sqlite-lint sqlite-lint.c -lsqlite3
 *
 * The functionality of this program may already exist in an off-the-shelf
 * tool, but a cursory search at time of writing did not turn up anything
 * suitable.
 */
#include <errno.h>
#include <fcntl.h>
#include <sqlite3.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

int main(int argc, char **argv) {
    int exit_code = -1;

    if (argc != 2 || strcmp(argv[1], "--help") == 0) {
        fprintf(stderr, "usage: %s filename\n"
                        " Check SQL statements in a file for correctness\n",
            argv[0]);
        return -1;
    }

    /* Measure the size of the input file. */
    struct stat st;
    if (stat(argv[1], &st) != 0) {
        fprintf(stderr, "failed to stat %s: ", argv[1]);
        perror(NULL);
        goto fail0;
    }
    size_t size = (size_t)st.st_size;

    /* Open the input file. */
    int fd = open(argv[1], O_RDONLY);
    if (fd == -1) {
        fprintf(stderr, "failed to open %s: ", argv[1]);
        perror(NULL);
        goto fail0;
    }

    /* Mmap the input. We could read it into a buffer, but this would require
     * dynamic memory allocations and other extra complexity.
     */
    void *addr = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (addr == MAP_FAILED) {
        fprintf(stderr, "failed to mmap %s: ", argv[1]);
        perror(NULL);
        goto fail1;
    }

    /* Open an in-memory database. Note that we do not care about persistence
     * of the database.
     */
    sqlite3 *db = NULL;
    if (sqlite3_open(":memory:", &db) != SQLITE_OK) {
        perror("failed to open in-memory database");
        goto fail2;
    }

    /* Try to prepare the statement. This should fail if the input has any
     * lexical errors.
     */
    sqlite3_stmt *stmt;
    int result = sqlite3_prepare_v2(db, addr, (int)size, &stmt, NULL);
    if (result != SQLITE_OK) {
        const char *msg = sqlite3_errmsg(db);
        /* Suppress errors resulting from a missing table as these are not
         * syntactic problems.
         */
        if (result != SQLITE_ERROR || strncmp(msg, "no such table: ",
                sizeof("no such table: ") - 1) != 0) {
            fprintf(stderr, "failed to prepare SQL statement: %s\n", msg);
            exit_code = -2;
            goto fail3;
        }
    }

    /* Success! */
    exit_code = 0;

       sqlite3_finalize(stmt);
fail3: sqlite3_close(db);
fail2: munmap(addr, size);
fail1: close(fd);
fail0: return exit_code;
}
