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

void show_register_dump(seL4_CPtr tcb) {
    seL4_UserContext regs;
    int err = seL4_TCB_ReadRegisters(tcb, false, 0, sizeof(regs) /
        sizeof(uintptr_t), &regs);
    if (err != 0) {
        SHOW("failed to retrieve register dump (error = %d)\n", err);
        return;
    }

    SHOW("     pc = %p\n", (void*)regs.pc);
    SHOW("     sp = %p\n", (void*)regs.sp);
    SHOW("     lr = %p\n", (void*)regs.r14);
    SHOW("     r0 = %p\n", (void*)regs.r0);
    SHOW("     r1 = %p\n", (void*)regs.r1);
    SHOW("     r2 = %p\n", (void*)regs.r2);
    SHOW("     r3 = %p\n", (void*)regs.r3);
    SHOW("     r4 = %p\n", (void*)regs.r4);
    SHOW("     r5 = %p\n", (void*)regs.r5);
    SHOW("     r6 = %p\n", (void*)regs.r6);
    SHOW("     r7 = %p\n", (void*)regs.r7);
    SHOW("     r8 = %p\n", (void*)regs.r8);
    SHOW("     r9 = %p\n", (void*)regs.r9);
    SHOW("    r10 = %p\n", (void*)regs.r10);
    SHOW("    r12 = %p\n", (void*)regs.r12);
    SHOW("    r14 = %p\n", (void*)regs.r14);
    SHOW("   cpsr = %p\n", (void*)regs.cpsr);
}
