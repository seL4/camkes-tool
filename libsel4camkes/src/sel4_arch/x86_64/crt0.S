/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
/*
 * A default seL4 crt0 for ia32. It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

    .global _camkes_start
    .extern _camkes_start_c

    .text

/* We get called with
   RDI: thread_id
   RSP: is 16 byte aligned
 */

_camkes_start:
    call _camkes_start_c
