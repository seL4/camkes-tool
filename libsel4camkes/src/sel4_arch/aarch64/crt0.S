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
 * A default seL4 crt0 for arm. It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

    .global _camkes_start
    .extern _camkes_tls_init
    .extern _start
    .extern sel4_vsyscall

    .text

_camkes_start:

    /* Save thread_id and entry_symbol so we can safely call tls_init */
    str     x0, [sp, #-8]!
    str     x0, [sp, #-8]! /* Maintain stack alignment */

    /* call tls_init with our thread_id (which is already in r0) */
    bl     _camkes_tls_init

    /* Restore registers */
    ldp     x0,  x1,  [sp, #16 * 0]


    /* null terminate auxv */
    mov     x5, #0
    str     x5, [sp, #-8]!
    str     x5, [sp, #-8]!
    /* give vsyscall location */
    ldr     x6, =sel4_vsyscall
    str     x6, [sp, #-8]!
    mov     x7, #32
    str     x7, [sp, #-8]!
    /* Null terminate envp */
    str     x5, [sp, #-8]!
    /* Give an environment string */
    ldr     x6, =environment_string
    str     x6, [sp, #-8]!
    /* Null terminate argument vector */
    str     x5, [sp, #-8]!
    /* Put on arguments */
    str     x0, [sp, #-8]!
    ldr     x6, =camkes_name
    str     x6, [sp, #-8]!
    /* Push argument count */
    mov     x6, #2
    str     x6, [sp, #-8]!
    /* Now go to actual _start */
    b       _start

/* .text Literal Pool */
.pool

    .data
    .align 4

camkes_name:
    .asciz "camkes"
environment_string:
    .asciz "seL4=1"
