/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/dataport.h>
#include <camkes/arch/dataport.h>
#include <platsupport/io.h>

int camkes_dataport_flush_cache(size_t start_offset, size_t size,
                                uintptr_t dataport_start, size_t dataport_size,
                                dma_cache_op_t cache_op)
{
    /* RISCV doesn't have page flushing operations */
    return 0;
}
