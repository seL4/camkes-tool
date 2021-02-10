/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes.h>

#include <string.h>

typedef struct breakpoint_state {
    seL4_Word vaddr;
    seL4_Word type;
    seL4_Word size;
    seL4_Word rw;
    seL4_Bool is_enabled;
} breakpoint_state_t;


static int check_read_memory(seL4_Word addr) {
    // TODO This doesn't deal with page boundaries
    uint32_t result = 0;
    asm volatile (
        "movl $0, %%eax;"
        "movl %[addr], %%ebx;"
        "movl (%%ebx), %%ecx;"
        // The code above will cause a fault to the mem handler if
        // the memory is not readable. The mem handler will set eax
        // appropriately
        "movl %%eax, %0;"
        : "=r" (result)
        : [addr] "r" (addr)
        : "eax", "ebx", "ecx"
    );
    return result;
}

static int check_write_memory(seL4_Word addr) {
    // TODO This doesn't deal with page boundaries
    uint32_t result = 0;
    asm volatile (
        "movl $0, %%eax;"
        "movl %[addr], %%ebx;"
        "movl (%%ebx), %%ecx;"
        "movl %%ecx, (%%ebx);"
        // The code above will cause a fault to the mem handler if
        // the memory is not readable. The mem handler will set eax
        // appropriately
        "movl %%eax, %0;"
        : "=r" (result)
        : [addr] "r" (addr)
        : "eax", "ebx", "ecx"
    );
    return result;
}

#ifdef CONFIG_HARDWARE_DEBUG_API
breakpoint_state_t breakpoints[seL4_NumDualFunctionMonitors];
#endif


static void breakpoint_init(void) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    for (int i = 0; i < seL4_NumDualFunctionMonitors; i++) {
        breakpoints[i].vaddr = 0;
        breakpoints[i].type = 0;
        breakpoints[i].size = 0;
        breakpoints[i].rw = 0;
        breakpoints[i].is_enabled = false;
    }
#endif
}

static int find_free_breakpoint(void) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    int bp = -1;
    for (int i = 0; i < seL4_NumDualFunctionMonitors; i++) {
        if (!breakpoints[i].is_enabled) {
            bp = i;
            break;
        }
    }
    return bp;
#else
    return -1;
#endif
}

static int get_breakpoint_num(seL4_Word vaddr UNUSED, seL4_Word type UNUSED,
                              seL4_Word size UNUSED, seL4_Word rw UNUSED) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    int bp = -1;
    for (int i = 0; i < seL4_NumDualFunctionMonitors; i++) {
        if (breakpoints[i].is_enabled && breakpoints[i].vaddr == vaddr &&
            breakpoints[i].type == type && breakpoints[i].size == size &&
            breakpoints[i].rw == rw) {
           bp = i;
           break;
        }
    }
    return bp;
#else
    return -1;
#endif
}

static void set_breakpoint_state(seL4_Word vaddr UNUSED, seL4_Word type UNUSED,
                                 seL4_Word size UNUSED, seL4_Word rw UNUSED, int bp UNUSED) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    breakpoints[bp].vaddr = vaddr;
    breakpoints[bp].type = type;
    breakpoints[bp].size = size;
    breakpoints[bp].rw = rw;
    breakpoints[bp].is_enabled = true;
#endif
}

static void clear_breakpoint_state(int bp UNUSED) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    breakpoints[bp].vaddr = 0;
    breakpoints[bp].type = 0;
    breakpoints[bp].size = 0;
    breakpoints[bp].rw = 0;
    breakpoints[bp].is_enabled = false;
#endif
}


void delegate__init() {
    breakpoint_init();
}

int delegate_read_memory(seL4_Word addr, seL4_Word length, delegate_mem_range_t *data) {
    if (length == 0 || length > MAX_MEM_RANGE) {
        ZF_LOGE("Invalid length %d", length);
        return 1;
    }
    if (check_read_memory(addr)) {
        return 1;
    } else {
        memcpy(data->data, (void *)addr, length);
        return 0;
    }
}

int delegate_write_memory(seL4_Word addr, seL4_Word length, delegate_mem_range_t data) {
    if (length == 0 || length > MAX_MEM_RANGE) {
        ZF_LOGE("Invalid length %d", length);
        return 1;
    }
    // If invalid memory, return with error
    if (check_write_memory(addr)) {
        return 1;
    } else {
        memcpy((void *) addr, (void *) data.data, length);
        return 0;
    }
}

void delegate_read_registers(seL4_Word tcb_cap, seL4_UserContext *registers) {
    int num_regs = sizeof(seL4_UserContext) / sizeof(seL4_Word);
    seL4_TCB_ReadRegisters(tcb_cap, false, 0, num_regs, registers);

    return;
}

void delegate_read_register(seL4_Word tcb_cap, seL4_Word *reg, seL4_Word reg_num) {
    int num_regs = sizeof(seL4_UserContext) / sizeof(seL4_Word);
    if (reg_num >= num_regs) {
        ZF_LOGE("Invalid register num: %zd", reg_num);
        return;
    }
    seL4_UserContext regs = {0};
    seL4_TCB_ReadRegisters(tcb_cap, false, 0, num_regs, &regs);
    seL4_Word *reg_word = (seL4_Word *) (& regs);
    *reg = reg_word[reg_num];
}

 int delegate_write_registers(seL4_Word tcb_cap, seL4_UserContext registers, int len) {
    // Get register values from IPC
    seL4_UserContext regs = {0};
    int num_regs = sizeof(seL4_UserContext) / sizeof(seL4_Word);
    seL4_TCB_ReadRegisters(tcb_cap, false, 0, num_regs, &regs);
    seL4_Word *reg_word = (seL4_Word *) (&regs);
    for (int i = 0; i < len; i++) {
        reg_word[i] = ((seL4_Word *)&regs)[i];
    }
    // Write registers
    int err = seL4_TCB_WriteRegisters(tcb_cap, false, 0, num_regs, &regs);
    if (err) {
        return 1;
    } else {
        return 0;
    }
}

int delegate_write_register(seL4_Word tcb_cap, seL4_Word data, seL4_Word reg_num) {
    int num_regs = sizeof(seL4_UserContext) / sizeof(seL4_Word);
    seL4_UserContext regs = {0};
    seL4_Word *reg_word = (seL4_Word *) (&regs);
    seL4_TCB_ReadRegisters(tcb_cap, false, 0, num_regs, &regs);
    // Change relevant register
    reg_word[reg_num] = data;
    int err = seL4_TCB_WriteRegisters(tcb_cap, false, 0, num_regs, &regs);
    if (err) {
        return 1;
    } else {
        return 0;
    }

}

int delegate_insert_break(seL4_Word tcb_cap, seL4_Word type, seL4_Word addr, seL4_Word size, seL4_Word rw) {
    int err = 0;
#ifdef CONFIG_HARDWARE_DEBUG_API
    // Insert the breakpoint
    int bp_num = find_free_breakpoint();
    if (bp_num == -1) {
        err = 1;
    } else {
        // Set the breakpoint
        err = seL4_TCB_SetBreakpoint(tcb_cap, (seL4_Uint16) bp_num, addr,
                                     type, size, rw);
        if (!err) {
            set_breakpoint_state(addr, type, size, rw, bp_num);
        }
        seL4_TCB_GetBreakpoint(tcb_cap, bp_num);
    }
#else
    err = -1;
#endif
    if (err) {
        return 1;
    } else {
        return 0;
    }
}

int delegate_remove_break(seL4_Word tcb_cap, seL4_Word type, seL4_Word addr, seL4_Word size, seL4_Word rw) {
    int err = 0;
#ifdef CONFIG_HARDWARE_DEBUG_API
    // Find the breakpoint
    int bp_num = get_breakpoint_num(addr, type, size, rw);
    if (bp_num == -1) {
        err = 1;
    }
    // Unset the breakpoint
    err = seL4_TCB_UnsetBreakpoint(tcb_cap, (seL4_Uint16) bp_num);
    if (!err) {
        clear_breakpoint_state(bp_num);
    }
#else
    err = -1;
#endif
    if (err) {
        return 1;
    } else {
        return 0;
    }
}


int delegate_resume(seL4_Word tcb_cap) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    seL4_TCB_ConfigureSingleStepping_t result = 
        seL4_TCB_ConfigureSingleStepping(tcb_cap, 0, 0);

    if (result.error) {
        return 1;
    } else {
        return 0;
    }
#endif
    return 1;
}

int delegate_step(seL4_Word tcb_cap) {
#ifdef CONFIG_HARDWARE_DEBUG_API
    seL4_TCB_ConfigureSingleStepping_t result = 
        seL4_TCB_ConfigureSingleStepping(tcb_cap, 0, 1);

    if (result.error) {
        return 1;
    } else {
        return 0;
    }
#endif
    return 1;

}

