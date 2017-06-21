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
#include <inttypes.h>

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name) {
    assert(name != NULL);

    uintptr_t rax = seL4_GetMR(0);
    uintptr_t rbx = seL4_GetMR(1);
    uintptr_t rcx = seL4_GetMR(2);
    uintptr_t rdx = seL4_GetMR(3);
    uintptr_t rsi = seL4_GetMR(4);
    uintptr_t rdi = seL4_GetMR(5);
    uintptr_t rbp = seL4_GetMR(6);
    uintptr_t  r8 = seL4_GetMR(7);
    uintptr_t  r9 = seL4_GetMR(8);
    uintptr_t r10 = seL4_GetMR(9);
    uintptr_t r11 = seL4_GetMR(10);
    uintptr_t r12 = seL4_GetMR(11);
    uintptr_t r13 = seL4_GetMR(12);
    uintptr_t r14 = seL4_GetMR(13);
    uintptr_t r15 = seL4_GetMR(14);
    uintptr_t rip = seL4_GetMR(15);
    uintptr_t rsp = seL4_GetMR(16);
    uintptr_t rflags = seL4_GetMR(17);
    int syscall = seL4_GetMR(18);
    SHOW("unknown syscall (%d) from %s (ID 0x%"PRIxPTR"), pc = %p\n"
         "   rax  = %p\n"
         "   rbx  = %p\n"
         "   rcx  = %p\n"
         "   rdx  = %p\n"
         "   rsi  = %p\n"
         "   rdi  = %p\n"
         "   rbp  = %p\n"
         "    r8  = %p\n"
         "    r9  = %p\n"
         "   r10  = %p\n"
         "   r11  = %p\n"
         "   r12  = %p\n"
         "   r13  = %p\n"
         "   r14  = %p\n"
         "   r15  = %p\n"
         "   rsp  = %p\n"
         " rflags = %p\n",
        syscall, name, thread_id, (void*)rip, (void*)rax, (void*)rbx,
        (void*)rcx, (void*)rdx, (void*)rsi, (void*)rdi, (void*)rbp,
        (void*)r8, (void*)r9, (void*)r10, (void*)r11, (void*)r12,
        (void*)r13, (void*)r14, (void*)r15, (void*)rsp, (void*)rflags);
}
