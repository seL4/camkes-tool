/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
