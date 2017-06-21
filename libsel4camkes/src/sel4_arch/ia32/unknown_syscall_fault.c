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

    uintptr_t eax = seL4_GetMR(0);
    uintptr_t ebx = seL4_GetMR(1);
    uintptr_t ecx = seL4_GetMR(2);
    uintptr_t edx = seL4_GetMR(3);
    uintptr_t esi = seL4_GetMR(4);
    uintptr_t edi = seL4_GetMR(5);
    uintptr_t ebp = seL4_GetMR(6);
    uintptr_t eip = seL4_GetMR(7);
    uintptr_t esp = seL4_GetMR(8);
    uintptr_t eflags = seL4_GetMR(9);
    int syscall = seL4_GetMR(10);
    SHOW("unknown syscall (%d) from %s (ID 0x%x), pc = %p\n"
         "   eax = %p\n"
         "   ebx  = %p\n"
         "   ecx  = %p\n"
         "   edx  = %p\n"
         "   esi  = %p\n"
         "   edi  = %p\n"
         "   ebp  = %p\n"
         "   esp  = %p\n"
         " eflags = %p\n",
        syscall, name, thread_id, (void*)eip, (void*)eax, (void*)ebx,
        (void*)ecx, (void*)edx, (void*)esi, (void*)edi, (void*)ebp, (void*)esp,
        (void*)eflags);
}
