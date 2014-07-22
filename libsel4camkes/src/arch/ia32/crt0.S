/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */
/*
 * A default crt0 for ia32. It does the bare minimum required to get into
 * main() with a sensible C environment.
 *
 * This file will only be linked in if:
 *   - no other file already provides a _start symbol, and
 *   - _start is an undefined external symbol (force this by passing
 *     "-u _start" to ld).
 */

#define __ASM__
#include <sel4/arch/constants.h>

#include <autoconf.h>

    .global _start

    .text

_start:

#ifdef CONFIG_CAPDL_LOADER_CC_REGISTERS
    /* If we've been passed the arguments in registers we need to shuffle them
     * onto the stack now as expected by main.
     */
    pushl   %edx
    pushl   %ecx
    pushl   %ebx
    pushl   %eax
#endif

    movw    $IPCBUF_GDT_SELECTOR, %ax
    movw    %ax, %gs

    /* Start main. */
    call    main

    /* Call _Exit() to suspend ourselves, as opposed to exit() that assumes we
     * are exiting the process and does some undesirable things like closing
     * stdout.
     */
    pushl   %eax
    call    _Exit

1:  jmp     1b
