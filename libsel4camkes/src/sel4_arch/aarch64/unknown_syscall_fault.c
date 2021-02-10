/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "../../arch_fault.h"
#include <assert.h>
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>
#include <inttypes.h>

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name)
{
    assert(name != NULL);

    uintptr_t x0 = seL4_GetMR(0);
    uintptr_t x1 = seL4_GetMR(1);
    uintptr_t x2 = seL4_GetMR(2);
    uintptr_t x3 = seL4_GetMR(3);
    uintptr_t x4 = seL4_GetMR(4);
    uintptr_t x5 = seL4_GetMR(5);
    uintptr_t x6 = seL4_GetMR(6);
    uintptr_t x7 = seL4_GetMR(7);
    uintptr_t pc = seL4_GetMR(8);
    uintptr_t sp = seL4_GetMR(9);
    uintptr_t lr = seL4_GetMR(10);
    uintptr_t spsr = seL4_GetMR(11);
    int syscall = seL4_GetMR(12);
    SHOW("unknown syscall (%d) from %s (ID 0x%"PRIxPTR"), pc = %p\n"
         "     x0 = %p\n"
         "     x1 = %p\n"
         "     x2 = %p\n"
         "     x3 = %p\n"
         "     x4 = %p\n"
         "     x5 = %p\n"
         "     x6 = %p\n"
         "     x7 = %p\n"
         "     sp = %p\n"
         "     lr = %p\n"
         "   spsr = %p\n",
         syscall, name, thread_id, (void *)pc, (void *)x0, (void *)x1, (void *)x2,
         (void *)x3, (void *)x4, (void *)x5, (void *)x6, (void *)x7, (void *)sp,
         (void *)lr, (void *)spsr);
}
