/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <utils/util.h>

/* XXX: When building with Clang, some initialisations get turned into calls to
 * `__aeabi_memset` that it then fails to provide. I suspect the problem lies in
 * the command line arguments we are passing it, but just squash the issue here
 * for now, by redirecting such calls back to `memset`.
 */
void *camkes_memset(void *s, int c, size_t n)
{
    return memset(s, c, n);
}
void *__aeabi_memset(void *s, int c, size_t n) WEAK ALIAS(camkes_memset);
