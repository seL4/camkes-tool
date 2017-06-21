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

#ifndef _ARCH_FAULT_H_
#define _ARCH_FAULT_H_

#include <sel4/sel4.h>
#include <stdio.h>

#define SHOW(args...) printf("FAULT HANDLER: " args)

void show_register_dump(seL4_CPtr tcb);

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name);

#endif
