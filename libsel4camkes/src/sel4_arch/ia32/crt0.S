/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
/*
 * A default seL4 crt0 for ia32. It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

#define __ASM__
#include <sel4/arch/constants.h>
#include <sel4/sel4_arch/constants.h>

#include <autoconf.h>
#include <sel4camkes/gen_config.h>

    .global _camkes_start
    .extern _camkes_start_c
    .text

_camkes_start:

/* The capdl loader starts us with a 16 byte aligned stack.
 * Before calling _camkes_tls_init (which doesn't go through _start),
 * we must ensure the stack is again 16 byte aligned.
 */

#ifndef CONFIG_CAPDL_LOADER_CC_REGISTERS
    /* If we've been passed the arguments on the stack we need to shuffle them
     * into registers for now */
    popl    %ecx

    /* This sub, combined with the popl above, causes the stack pointer
     * to be offset by 8 from a 16 byte aligned value.
     */
    sub $12, %esp
#else
    /* As the stack pointer was initially 16 byte aligned, this add causes
     * it to be offset by 8 from a 16 byte aligned value.
     */
    sub $8, %esp
#endif

    /* Regardless of the calling convention, at this point the stack
     * pointer is offset by 8 bytes from a 16 byte aligned value.
     */

    /* Save thread_id and entry_point so we can
     * put them into argv later */
    pushl %ecx
    pushl %ecx

    /* The two push instructions decreased the stack pointer by 8 in
     * total. As the stack pointer was offset by 8 bytes from a 16
     * byte aligned value prior to those instructions, at this point
     * it is 16 byte aligned, so we can safely call the function.
     */
    call _camkes_start_c
