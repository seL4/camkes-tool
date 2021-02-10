/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "../../arch_fault.h"
#include <assert.h>
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name)
{
    assert(name != NULL);

    uintptr_t pc = seL4_GetMR(0);
    uintptr_t sp = seL4_GetMR(1);
    uintptr_t lr = seL4_GetMR(2);
    uintptr_t a0 = seL4_GetMR(3);
    uintptr_t a1 = seL4_GetMR(4);
    uintptr_t a2 = seL4_GetMR(5);
    uintptr_t a3 = seL4_GetMR(6);
    uintptr_t a4 = seL4_GetMR(7);
    uintptr_t a5 = seL4_GetMR(8);
    uintptr_t a6 = seL4_GetMR(9);
    int syscall = seL4_GetMR(10);
    SHOW("unknown syscall (%d) from %s (ID 0x%x), pc = %p\n"
         "     a0 = %p\n"
         "     a1 = %p\n"
         "     a2 = %p\n"
         "     a3 = %p\n"
         "     a4 = %p\n"
         "     a5 = %p\n"
         "     a6 = %p\n"
         "     sp = %p\n"
         "     lr = %p\n",
         syscall, name, thread_id, (void *)pc, (void *)a0, (void *)a1, (void *)a2,
         (void *)a3, (void *)a4, (void *)a5, (void *)a6, (void *)sp,
         (void *)lr);
}
