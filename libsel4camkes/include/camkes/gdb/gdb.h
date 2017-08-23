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
#pragma once

#include <sel4/sel4.h>
#include <stdint.h>
#include <stdbool.h>
#include <camkes/gdb/delegate_types.h>

#define NO_BREAKPOINT -1
#define USER_BREAKPOINT 0
#define BREAKPOINT_INSTRUCTION 0xCC
#define MAX_ARGS 20   
#define COMMAND_START                   1
#define HEX_STRING						16
#define DEC_STRING						10
#define CHAR_HEX_SIZE					2

// Colour coding for response packets from GDB stub
//#define GDB_RESPONSE_START      "\x1b[31m"
//#define GDB_RESPONSE_END        "\x1b[0m"
#define GDB_RESPONSE_START      ""
#define GDB_RESPONSE_END        ""

// Ok packet for GDB
#define GDB_ACK                 "+"
#define GDB_NACK                "-" 
#define x86_VALID_REGISTERS     10
#define x86_GDB_REGISTERS       13
#define x86_MAX_REGISTERS       16
#define x86_INVALID_REGISTER    10
#define x86_NUM_HW_BRK          4
#define x86_SW_BREAK            0xCC

#define HARDWARE_BREAKPOINT      0x1
#define GENERAL_PROTECTION_FAULT 0xD

typedef enum {
    stop_none,
    stop_sw_break,
    stop_hw_break,
    stop_step,
    stop_watch
} stop_reason_t;

typedef enum {
    gdb_SoftwareBreakpoint,
    gdb_HardwareBreakpoint,
    gdb_WriteWatchpoint,
    gdb_ReadWatchpoint,
    gdb_AccessWatchpoint
} gdb_BreakpointType;

#define GETCHAR_BUFSIZ 512

typedef struct gdb_buffer {
    uint32_t length;
    uint32_t checksum_count;
    uint32_t checksum_index;
    char data[GETCHAR_BUFSIZ];
} gdb_buffer_t;

extern gdb_buffer_t buf;

typedef struct {
    /* Cap of currently selected thread in components cspace */
    seL4_Word current_thread_tcb;
    /* Current pc of the currently selected thread */
    seL4_Word current_pc;
    /* current thread's hw debugging step mode */
    bool current_thread_step_mode;
    /* Fault reason for the currently selected thread */
    stop_reason_t stop_reason;
    /* If fault was watch fault, then this is the address */
    seL4_Word stop_watch_addr;
    /* Callback function to wake thread's fault handler */
    int (*sem_post)(void);
} gdb_state_t;

int delegate_write_memory(seL4_Word addr, seL4_Word length, delegate_mem_range_t data);
int delegate_read_memory(seL4_Word addr, seL4_Word length, delegate_mem_range_t *data);
void delegate_read_registers(seL4_Word tcb_cap, seL4_UserContext *registers);
void delegate_read_register(seL4_Word tcb_cap, seL4_Word *reg, seL4_Word reg_num);
int delegate_write_registers(seL4_Word tcb_cap, seL4_UserContext registers, int len);
int delegate_write_register(seL4_Word tcb_cap, seL4_Word data, seL4_Word reg_num);
int delegate_insert_break(seL4_Word tcb_cap, seL4_Word type, seL4_Word addr, seL4_Word size, seL4_Word rw);
int delegate_remove_break(seL4_Word tcb_cap, seL4_Word type, seL4_Word addr, seL4_Word size, seL4_Word rw);
int delegate_resume(seL4_Word tcb_cap);
int delegate_step(seL4_Word tcb_cap);



int handle_gdb(gdb_state_t *gdb_state);
int gdb_handle_fault(gdb_state_t *gdb_state);