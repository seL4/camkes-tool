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
#define MAX_MEM_RANGE 100

typedef struct delegate_mem_range {
    uint8_t data[MAX_MEM_RANGE];
} delegate_mem_range_t;
