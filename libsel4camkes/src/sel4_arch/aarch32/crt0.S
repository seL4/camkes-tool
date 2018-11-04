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
    push    {r0}
    push    {r0} /* Maintain stack alignment */

    /* call tls_init with our thread_id (which is already in r0) */
    blx     _camkes_tls_init

    /* Restore registers */
    pop     {r0}

    /* To ensure we end up with a correctly 8 byte aligned stack at the end we
     * need to pad by one word here */
    push    {r0}

    /* null terminate auxv */
    mov     r5, #0
    push    {r5}
    push    {r5}
    /* give vsyscall location */
    ldr     r6, =sel4_vsyscall
    push    {r6}
    mov     r7, #32
    push    {r7}
    /* Null terminate envp */
    push    {r5}
    /* Give an environment string */
    ldr     r6, =environment_string
    push    {r6}
    /* Null terminate argument vector */
    push    {r5}
    /* Put on arguments */
    push    {r0}
    ldr     r6, =camkes_name
    push    {r6}
    /* Push argument count */
    mov     r6, #2
    push    {r6}
    /* Now go to actual _start */
    ldr     pc, =_start

/* .text Literal Pool */
.pool

    .data
    .align 4

camkes_name:
    .asciz "camkes"
environment_string:
    .asciz "seL4=1"
