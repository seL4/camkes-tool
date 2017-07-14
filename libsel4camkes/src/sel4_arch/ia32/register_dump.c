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

    SHOW("      eip = %p\n", (void*)regs.eip);
    SHOW("      esp = %p\n", (void*)regs.esp);
    SHOW("      eax = %p\n", (void*)regs.eax);
    SHOW("      ebx = %p\n", (void*)regs.ebx);
    SHOW("      ecx = %p\n", (void*)regs.ecx);
    SHOW("      edx = %p\n", (void*)regs.edx);
    SHOW("      esi = %p\n", (void*)regs.esi);
    SHOW("      edi = %p\n", (void*)regs.edi);
    SHOW("      ebp = %p\n", (void*)regs.ebp);
    SHOW("       fs = %p\n", (void*)regs.fs);
    SHOW("       gs = %p\n", (void*)regs.gs);
    SHOW("   eflags = %p\n", (void*)regs.eflags);
    SHOW(" tls_base = %p\n", (void*)regs.tls_base);
}
