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

#include <stdio.h>
#include <stdlib.h>

void ffifail(unsigned char *c, long clen, unsigned char *a, long alen) {
    printf("CakeML called fail\n");
    exit(-1);
}

void cml_exit(int arg) {
    printf("Called cml_exit\n");
    exit(arg);
}
