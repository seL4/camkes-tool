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
/*
 * A default seL4 crt0 for ia32. It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

#define __ASM__
#include <sel4/arch/constants.h>
#include <sel4/sel4_arch/constants.h>

#include <autoconf.h>

    .global _camkes_start
    .extern _camkes_tls_init
    .extern _start
    .extern sel4_vsyscall

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

    movw    $IPCBUF_GDT_SELECTOR, %ax
    movw    %ax, %fs

    /* Save thread_id and entry_point so we can
     * put them into argv later */
    pushl %ecx

    /* Setup per thread tls */
    pushl %ecx

    /* The two push instructions decreased the stack pointer by 8 in
     * total. As the stack pointer was offset by 8 bytes from a 16
     * byte aligned value prior to those instructions, at this point
     * it is 16 byte aligned, so we can safely call the function.
     */
    call _camkes_tls_init

    /* If we get back here we no longer care about stack alignment.
     * This is because the next function we call is _start, and on
     * ia32, _start checks and corrects the stack pointer alignment.
     */

    addl $4, %esp

    /* Restore */
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
    pushl %eax
    leal camkes_name, %ecx
    pushl %ecx
    /* Push argument count */
    pushl $2
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
