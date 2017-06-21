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

#include "../../arch_fault.h"
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

void show_register_dump(seL4_CPtr tcb) {
    seL4_UserContext regs;
    int err = seL4_TCB_ReadRegisters(tcb, false, 0, sizeof(regs) /
        sizeof(uintptr_t), &regs);
    if (err != 0) {
        SHOW("failed to retrieve register dump (error = %d)\n", err);
        return;
    }

    SHOW("      rip = %p\n", (void*)regs.rip);
    SHOW("      rsp = %p\n", (void*)regs.rsp);
    SHOW("      rax = %p\n", (void*)regs.rax);
    SHOW("      rbx = %p\n", (void*)regs.rbx);
    SHOW("      rcx = %p\n", (void*)regs.rcx);
    SHOW("      rdx = %p\n", (void*)regs.rdx);
    SHOW("      rsi = %p\n", (void*)regs.rsi);
    SHOW("      rdi = %p\n", (void*)regs.rdi);
    SHOW("       r8 = %p\n", (void*)regs.r8);
    SHOW("       r9 = %p\n", (void*)regs.r9);
    SHOW("      r10 = %p\n", (void*)regs.r10);
    SHOW("      r11 = %p\n", (void*)regs.r11);
    SHOW("      r12 = %p\n", (void*)regs.r12);
    SHOW("      r13 = %p\n", (void*)regs.r13);
    SHOW("      r14 = %p\n", (void*)regs.r14);
    SHOW("      r15 = %p\n", (void*)regs.r15);
    SHOW("   rflags = %p\n", (void*)regs.rflags);
    SHOW(" tls_base = %p\n", (void*)regs.tls_base);
}
