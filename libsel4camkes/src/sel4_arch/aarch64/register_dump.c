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
    SHOW("lr(x30) = %p\n", (void*)regs.x30);
    SHOW("     x0 = %p\n", (void*)regs.x0);
    SHOW("     x1 = %p\n", (void*)regs.x1);
    SHOW("     x2 = %p\n", (void*)regs.x2);
    SHOW("     x3 = %p\n", (void*)regs.x3);
    SHOW("     x4 = %p\n", (void*)regs.x4);
    SHOW("     x5 = %p\n", (void*)regs.x5);
    SHOW("     x6 = %p\n", (void*)regs.x6);
    SHOW("     x7 = %p\n", (void*)regs.x7);
    SHOW("     x8 = %p\n", (void*)regs.x8);
    SHOW("     x9 = %p\n", (void*)regs.x9);
    SHOW("    x10 = %p\n", (void*)regs.x10);
    SHOW("    x11 = %p\n", (void*)regs.x11);
    SHOW("    x12 = %p\n", (void*)regs.x12);
    SHOW("    x13 = %p\n", (void*)regs.x13);
    SHOW("    x14 = %p\n", (void*)regs.x14);
    SHOW("    x15 = %p\n", (void*)regs.x15);
    SHOW("    x16 = %p\n", (void*)regs.x16);
    SHOW("    x17 = %p\n", (void*)regs.x17);
    SHOW("    x18 = %p\n", (void*)regs.x18);
    SHOW("    x19 = %p\n", (void*)regs.x19);
    SHOW("    x20 = %p\n", (void*)regs.x20);
    SHOW("    x21 = %p\n", (void*)regs.x21);
    SHOW("    x22 = %p\n", (void*)regs.x22);
    SHOW("    x23 = %p\n", (void*)regs.x23);
    SHOW("    x24 = %p\n", (void*)regs.x24);
    SHOW("    x25 = %p\n", (void*)regs.x25);
    SHOW("    x26 = %p\n", (void*)regs.x26);
    SHOW("    x27 = %p\n", (void*)regs.x27);
    SHOW("    x28 = %p\n", (void*)regs.x28);
    SHOW("    x29 = %p\n", (void*)regs.x29);
    SHOW("    x30 = %p\n", (void*)regs.x30);
    SHOW("   cpsr = %p\n", (void*)regs.spsr);
}
