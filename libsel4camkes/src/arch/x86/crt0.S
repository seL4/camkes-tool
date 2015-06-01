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
 * A default seL4 crt0 for ia32. It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

#define __ASM__
#include <sel4/arch/constants.h>

#include <autoconf.h>

    .global _camkes_start
    .extern _start
    .extern sel4_vsyscall

    .text

_camkes_start:

#ifndef CONFIG_CAPDL_LOADER_CC_REGISTERS
    /* If we've been passed the arguments on the stack we need to shuffle them
     * into registers for now */
    popl    %eax
    popl    %ebx
    popl    %ecx
#endif

    movw    $IPCBUF_GDT_SELECTOR, %dx
    movw    %dx, %gs

    /* Save thread_id and entry_point so we can
     * put them into argv later */
    pushl %eax
    pushl %ebx

    /* Setup per thread tls */
    pushl %eax
    call *%ecx
    addl $4, %esp

    /* Restore */
    popl %ebx
    popl %eax

    /* Null terminate auxiliary vector */
    pushl $0
    pushl $0
    /* Set __sysinfo */
    leal  sel4_vsyscall, %ecx
    pushl %ecx
    pushl $32 /* AT_SYSINFO */
    /* Null terminate environment vector */
    pushl $0
    leal  environment_string, %ecx
    pushl %ecx
    /* Null terminate argument vector */
    pushl $0
    /* Construct arguments */
    pushl %ebx
    pushl %eax
    leal camkes_name, %ecx
    pushl %ecx
    /* Push argument count */
    pushl $3
    /* No atexit */
    movl $0, %edx

    /* Go to the real start function */
    jmp _start

    .data
    .align 4

camkes_name:
    .asciz "camkes"
environment_string:
    .asciz "seL4=1"
