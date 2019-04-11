/*
 * Copyright 2019, Data61
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
 * Camkes crt0 for riscv It does the bare minimum required to emulate
 * a typical startup environment and jump to the regular _start symbol
 */

#include <autoconf.h>

#if __riscv_xlen == 32
#define LW lw
#define SW sw
#define REGSIZE 4
#else
#define LW ld
#define SW sd
#define REGSIZE 8
#endif

    .global _camkes_start
    .extern sel4_vsyscall
    .extern _start
    .extern sel4_vsyscall

    .text

_camkes_start:

/* Set gp for relaxation. See
 * https://www.sifive.com/blog/2017/08/28/all-aboard-part-3-linker-relaxation-in-riscv-toolchain/
 */
.option push
.option norelax
1:auipc gp, %pcrel_hi(__global_pointer$)
  addi  gp, gp, %pcrel_lo(1b)
.option pop
    /* Create a 10 word stack frame */
    addi sp, sp, -(10*REGSIZE)
    /* Save thread ID for later */
    SW   a0, (0)(sp)

    /* Setup per thread tls (argument is already in rdi)
     *
     * For threads other than the component's control thread (ie.
     * interface threads and fault handler threads), this does
     * not return, but instead calls post_main directly.
     */
    jal _camkes_tls_init

    /* read thread ID out of stack */
    LW   a0, (0)(sp)

    /* argc */
    li   a1, 2
    SW   a1, 0(sp)
    /* prog name */
    la   a1, prog_name
    SW   a1, (1*REGSIZE)(sp)
    /* Thread id register */
    SW   a0, (2*REGSIZE)(sp)

    /* Null-terminate arg vector */
    SW   x0, (3*REGSIZE)(sp)

    /* Give an environment string */
    la   a1, environment_string
    SW   a1, (4*REGSIZE)(sp)

    /* Null terminate envp */
    SW   x0, (5*REGSIZE)(sp)

    /* give vsyscall location */
    li   a1, 32
    SW   a1, (6*REGSIZE)(sp)
    la   a1, sel4_vsyscall
    SW   a1, (7*REGSIZE)(sp)

    /* null terminate auxv */
    SW   x0, (8*REGSIZE)(sp)
    SW   x0, (9*REGSIZE)(sp)

    /* Now go to actual _start */
    j       _start

/* .text Literal Pool */
    .data
    .align  8
environment_string:
    .asciz "seL4=1"
prog_name:
    .asciz "camkes"
