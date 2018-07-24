/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
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
