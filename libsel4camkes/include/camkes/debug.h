/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdint.h>

/* Helper function to insert a software breakpoint */

#define camkes_software_breakpoint() asm("int3")

