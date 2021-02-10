/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <byteswap.h>

#define IO_FAILURE 1
#define IO_SUCCESS 0

void ffiopen_in(unsigned char *c, long clen, unsigned char *a, long alen) {
    int fd = open((const char *) c, O_RDONLY);
    if (fd < 0) {
        a[0] = IO_SUCCESS;
        uint64_t result = bswap_64(fd);
        memcpy(a + 1, &result, sizeof(result));
    } else {
        a[0] = IO_FAILURE;
    }
}

void ffiopen_out(unsigned char *c, long clen, unsigned char *a, long alen) {
    int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC);
    if (0 <= fd) {
        a[0] = IO_SUCCESS;
        uint64_t result = bswap_64(fd);
        memcpy(a + 1, &result, sizeof(result));
    } else {
        a[0] = IO_FAILURE;
    }
}

void ffiread(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t fd_raw;
    uint16_t n_raw;
    memcpy(&fd_raw, c, sizeof(fd_raw));
    memcpy(&n_raw, a, sizeof(n_raw));
    int fd = bswap_64(fd_raw);
    int n = bswap_16(n_raw);
    int nread = read(fd, a + 4, n);
    if (nread < 0) {
        a[0] = IO_FAILURE;
    } else {
        a[0] = IO_SUCCESS;
        uint16_t result = bswap_16(nread);
        memcpy(a + 1, &result, sizeof(result));
    }
}

void ffiwrite(unsigned char *c, long clen, unsigned char *a, long alen){
    uint64_t fd_raw;
    uint16_t n_raw;
    uint16_t off_raw;
    memcpy(&fd_raw, c, sizeof(fd_raw));
    memcpy(&n_raw, a, sizeof(n_raw));
    memcpy(&off_raw, a + 2, sizeof(off_raw));
    int fd = bswap_64(fd_raw);
    int n = bswap_16(n_raw);
    int off = bswap_16(off_raw);
    int nw = write(fd, a + 4 + off, n);
    if (nw < 0) {
        a[0] = IO_FAILURE;
    } else {
        a[0] = IO_SUCCESS;
        uint16_t result = bswap_16(nw);
        memcpy(a + 1, &result, sizeof(result));
    }
}

void fficlose(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t fd_raw;
    memcpy(&fd_raw, c, sizeof(fd_raw));
    int fd = bswap_64(fd_raw);
    a[0] = close(fd) == 0 ? IO_SUCCESS : IO_FAILURE;
}
