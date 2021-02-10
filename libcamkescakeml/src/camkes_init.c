/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/init.h>

/* Wrappers around the init functions. We need wrappers to handle CakeML not being about
 * to call arbitrarily named functions and to massage the return type back into the bytes array */

void ffipre_init_interface_sync(unsigned char *c, long clen, unsigned char *a, long alen) {
    int result = pre_init_interface_sync();
    *a = (unsigned char)result;
}

void ffipost_init_interface_sync(unsigned char *c, long clen, unsigned char *a, long alen) {
    int result = post_init_interface_sync();
    *a = (unsigned char)result;
}
