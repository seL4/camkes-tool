/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <byteswap.h>

/* argc and argv are exported in cake.S */
extern unsigned int argc;
extern char **argv;

void ffiget_arg_count(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint16_t result = bswap_16(argc);
    memcpy(a, &result, sizeof(result));
}

void ffiget_arg_length(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint16_t arg;
    memcpy(&arg, a, sizeof(arg));
    arg = bswap_16(arg);
    uint16_t len_result = bswap_16(strlen(argv[arg]));
    memcpy(a, &len_result, sizeof(len_result));
}

void ffiget_arg(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint16_t arg;
    memcpy(&arg, a, sizeof(arg));
    arg = bswap_16(arg);
    strcpy(a, argv[arg]);
}
