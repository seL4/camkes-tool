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
#include <camkes/gdb/gdb.h>

/* send message to gdb client */
void gdb_printf(const char *format, ...);

/* Initialise serial for debugger */
void serial_init(gdb_state_t *gdb_state);

/* Mutex around serial hardware */
int serial_lock(void);
int serial_unlock(void);

/* CAmkES hw IRQ function */
int serial_irq_acknowledge(void);