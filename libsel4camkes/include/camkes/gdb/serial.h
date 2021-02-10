/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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