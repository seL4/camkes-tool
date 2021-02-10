/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/sel4.h>
#include <stdio.h>

#define FAULT_PREFIX "FAULT HANDLER: "
#define SHOW(args...) printf(FAULT_PREFIX args)

void show_unknown_syscall_fault(seL4_CPtr thread_id, const char *name);
