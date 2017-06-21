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
#include <assert.h>
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name) {
    assert(name != NULL);

    uintptr_t r0 = seL4_GetMR(0);
    uintptr_t r1 = seL4_GetMR(1);
    uintptr_t r2 = seL4_GetMR(2);
    uintptr_t r3 = seL4_GetMR(3);
    uintptr_t r4 = seL4_GetMR(4);
    uintptr_t r5 = seL4_GetMR(5);
    uintptr_t r6 = seL4_GetMR(6);
    uintptr_t r7 = seL4_GetMR(7);
    uintptr_t pc = seL4_GetMR(8);
    uintptr_t sp = seL4_GetMR(9);
    uintptr_t lr = seL4_GetMR(10);
    uintptr_t cpsr = seL4_GetMR(11);
    int syscall = seL4_GetMR(12);
    SHOW("unknown syscall (%d) from %s (ID 0x%x), pc = %p\n"
         "     r0 = %p\n"
         "     r1 = %p\n"
         "     r2 = %p\n"
         "     r3 = %p\n"
         "     r4 = %p\n"
         "     r5 = %p\n"
         "     r6 = %p\n"
         "     r7 = %p\n"
         "     sp = %p\n"
         "     lr = %p\n"
         "   cpsr = %p\n",
        syscall, name, thread_id, (void*)pc, (void*)r0, (void*)r1, (void*)r2,
        (void*)r3, (void*)r4, (void*)r5, (void*)r6, (void*)r7, (void*)sp,
        (void*)lr, (void*)cpsr);
}
