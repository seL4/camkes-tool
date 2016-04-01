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

/* We get called with
   RDI: thread_id
 */

_camkes_start:

    /* Save thread ID for later */
    pushq %rdi
    /* Setup per thread tls (argument is already in rdi) */
    call _camkes_tls_init
    /* Restore thread ID */
    popq %rax

    /* Null terminate auxiliary vector */
    pushq $0
    pushq $0
    /* Set __sysinfo */
    leaq  sel4_vsyscall, %rcx
    pushq %rcx
    pushq $32 /* AT_SYSINFO */
    /* Null terminate environment vector */
    pushq $0
    leaq  environment_string, %rcx
    pushq %rcx
    /* Null terminate argument vector */
    pushq $0
    /* Construct arguments */
    pushq %rax
    leaq camkes_name, %rcx
    pushq %rcx
    /* Push argument count */
    pushq $2
    /* No atexit */
    movq $0, %rdx

    /* Go to the real start function */
    jmp _start

    .data
    .align 4

camkes_name:
    .asciz "camkes"
environment_string:
    .asciz "seL4=1"
