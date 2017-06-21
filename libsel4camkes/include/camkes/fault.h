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

#ifndef _CAMKES_FAULT_H_
#define _CAMKES_FAULT_H_

#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdint.h>

/* A named region of an address space. See usage below. */
typedef struct {
    uintptr_t start;
    uintptr_t end;
    const char *name;
} camkes_memory_region_t;

/* Print diagnostic information about a capability or virtual memory fault that
 * has just been caught. The assumption is that this fault's information is
 * still in your IPC buffer. This function is only expected to be called from
 * glue code.
 *
 *  info - The message information from the fault message
 *  thread_id - Numerical identifier of the faulting thread
 *  name - Human-readable name of the faulting thread
 *  tcb_caps_available - Whether the identifier of the thread is a usable cap
 *  memory_map - Description of the source's address space (can be NULL)
 *
 * Note that if `memory_map` is provided, the final entry of the array should
 * be a sentinel region with `start == end == 0`.
 */
void camkes_show_fault(seL4_MessageInfo_t info, seL4_CPtr thread_id,
    const char *name, bool tcb_caps_available,
    const camkes_memory_region_t *memory_map);

#endif
