/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "arch_fault.h"
#include <assert.h>
#include <camkes/fault.h>
#include <limits.h>
#include <sel4/sel4.h>
#include <sel4debug/register_dump.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <inttypes.h>

/* This function is provided by generated code. */
extern const char *get_instance_name(void);

/* Display information about a fault address, situating within the given memory
 * map. The memory map is not assumed to be ordered.
 */
static void show_fault_location(const camkes_memory_region_t *memory_map,
                                uintptr_t address)
{
    assert(memory_map != NULL);

    /* Calculate the number of entries in the memory map. */
    size_t memory_map_sz = 0;
    for (const camkes_memory_region_t *reg = memory_map;
         reg->start != 0 || reg->end != 0;
         reg++, memory_map_sz++);

    /* Determine how many characters are needed to print a pointer
     * (n-bit compatibility).
     */
    int ptr_bytes = snprintf(NULL, 0, "%"PRIxPTR, UINTPTR_MAX);
    assert(ptr_bytes > 0 && "0-bit pointers; huh?");

    SHOW("  memory map:\n");

    /* How many entries we've currently printed. */
    size_t printed = 0;

    /* The last upper address we saw. We're going to work our way down through
     * the regions to give the user a logical display of their address space.
     */
    uintptr_t limit = UINTPTR_MAX;

    uintptr_t last_start = 0;
    while (printed < memory_map_sz) {
        const camkes_memory_region_t *current = NULL;

        for (const camkes_memory_region_t *reg = memory_map;
             reg->start != 0 || reg->end != 0; reg++) {

            assert(reg->start <= reg->end && "inverted region in memory map");

            /* If the current region is the uppermost thing we've seen thus far
             * that we haven't printed...
             */
            if (reg->end <= limit && (current == NULL ||
                                      reg->end > current->end)) {
                current = reg;
            }
        }

        assert(current != NULL && "overlapping or illegal regions in memory map");

        if (current->end != last_start - 1) {
            if (limit != UINTPTR_MAX) {
                SHOW("    |   <undescribed>\n");
            }
            SHOW("    +-- 0x%.*"PRIxPTR" --\n", ptr_bytes, current->end);
        }
        SHOW("    |   %s\n", current->name);
        if (address >= current->start && address <= current->end) {
            SHOW("    |   FAULT @ 0x%.*"PRIxPTR"\n", ptr_bytes, address);
        }
        SHOW("    +-- 0x%.*"PRIxPTR" --\n", ptr_bytes, current->start);
        last_start = current->start;
        limit = current->end - 1;
        printed++;
    }
}

void camkes_show_fault(seL4_MessageInfo_t info, seL4_CPtr thread_id,
                       const char *name, bool tcb_caps_available,
                       const camkes_memory_region_t *memory_map)
{

    const char *safe_name = name == NULL ? "<unknown>" : name;

    int label = seL4_MessageInfo_get_label(info);
    switch (label) {

    case seL4_Fault_CapFault: {
        /* From section 5.2.1 of the seL4 manual. */
        uintptr_t pc = (uintptr_t)seL4_GetMR(0);
        seL4_CPtr slot = (seL4_CPtr)seL4_GetMR(1);
        bool receive = seL4_GetMR(2) == 1;

        /* From section 3.4 of the seL4 manual. */
        int cause = seL4_GetMR(3);
        switch (cause) {

        case seL4_InvalidRoot:
            SHOW("cap fault (invalid root) in %s phase from %s.%s (ID "
                 "0x%"PRIxPTR"), pc = %p, slot = 0x%"PRIxPTR"\n", receive ? "receive" :
                 "send", get_instance_name(), safe_name, thread_id,
                 (void *)pc, slot);
            break;

        case seL4_MissingCapability: {
            unsigned unresolved = seL4_GetMR(4);
            SHOW("cap fault (missing capability with %u unresolved "
                 "bits) from %s.%s (ID 0x%"PRIxPTR"), pc = %p, slot = 0x%"PRIxPTR"\n",
                 unresolved, get_instance_name(), safe_name, thread_id,
                 (void *)pc, slot);
            break;
        }

        case seL4_DepthMismatch: {
            unsigned unresolved = seL4_GetMR(4);
            unsigned resolved = seL4_GetMR(5);
            SHOW("cap fault (depth mismatch with %u unresolved bits "
                 "and %u resolved bits) from %s.%s (ID 0x%"PRIxPTR"), pc = %p, "
                 "slot = 0x%"PRIxPTR"\n", unresolved, resolved, get_instance_name(),
                safe_name, thread_id, (void*)pc, slot);
            break;
        }

            case seL4_GuardMismatch: {
            unsigned unresolved = seL4_GetMR(4);
            seL4_Word guard = seL4_GetMR(5);
            unsigned guard_size = seL4_GetMR(6);
            SHOW("cap fault (guard mismatch with %u unresolved bits "
                "and %u bit guard of 0x%"PRIxPTR") from %s.%s (ID 0x%"PRIxPTR"), pc = "
                "%p, slot = 0x%"PRIxPTR"\n", unresolved, guard_size, guard,
                get_instance_name(), safe_name, thread_id, (void*)pc, slot);
            break;
        }

            default:
                SHOW("cap fault (unknown cause %d; API bug?) from %s.%s "
                    "(ID 0x%"PRIxPTR"), pc = %p, slot = 0x%"PRIxPTR"\n", label,
                    get_instance_name(), safe_name, thread_id, (void*)pc,
                    slot);
                break;

        }
        break;
    }

        case seL4_Fault_VMFault: {
        uintptr_t pc = seL4_GetMR(0);
        uintptr_t addr = seL4_GetMR(1);
        bool instruction_fault = seL4_GetMR(2) == 1;
        uintptr_t fsr = seL4_GetMR(3);
        SHOW("%s fault from %s.%s (ID 0x%"PRIxPTR") on address %p, pc = %p, fsr = "
            "0x%"PRIxPTR"\n", instruction_fault ? "instruction" : "data",
            get_instance_name(), safe_name, thread_id, (void*)addr,
            (void*)pc, fsr);
        if (tcb_caps_available) {
            sel4debug_dump_registers_prefix(thread_id, FAULT_PREFIX);
        } else {
            SHOW("register dump unavailable (no cap to target TCB)\n");
        }
        if (memory_map != NULL) {
            show_fault_location(memory_map, addr);
        }
        break;
    }

        case seL4_Fault_UnknownSyscall:
            show_unknown_syscall_fault(thread_id, name);
            break;

        case seL4_Fault_UserException: {
        uintptr_t pc = seL4_GetMR(0);
        uintptr_t sp = seL4_GetMR(1);
        uintptr_t flags = seL4_GetMR(2);
        int exc_no = seL4_GetMR(3);
        int exc_code = seL4_GetMR(4);

        SHOW("user exception (number %d, code %d) from %s.%s (ID 0x%"PRIxPTR"), "
            "pc = %p, sp = %p, flags = %p\n", exc_no, exc_code,
            get_instance_name(), safe_name, thread_id, (void*)pc, (void*)sp,
            (void*)flags);
        break;
    }

        default:
            SHOW("unknown message from %s.%s (ID 0x%"PRIxPTR"); misconfigured fault "
                "handler?\n", get_instance_name(), safe_name, thread_id);
    }
}
