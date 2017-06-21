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

#include <string.h>
#include <utils/util.h>

/* XXX: When building with Clang, some initialisations get turned into calls to
 * `__aeabi_memset` that it then fails to provide. I suspect the problem lies in
 * the command line arguments we are passing it, but just squash the issue here
 * for now, by redirecting such calls back to `memset`.
 */
void *camkes_memset(void *s, int c, size_t n) {
    return memset(s, c, n);
}
void *__aeabi_memset(void *s, int c, size_t n) WEAK ALIAS(camkes_memset);
