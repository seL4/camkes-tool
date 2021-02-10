/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/sel4.h>
#include <stdint.h>
#define MAX_MEM_RANGE 100

typedef struct delegate_mem_range {
    uint8_t data[MAX_MEM_RANGE];
} delegate_mem_range_t;
