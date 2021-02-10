/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/arch/io.h>

int camkes_arch_io_port_in(uint32_t port, int io_size, uint32_t *result)
{
    /* ARM does not support IO ports */
    return -1;
}

int camkes_arch_io_port_out(uint32_t port, int io_size, uint32_t val)
{
    /* ARM does not support IO ports */
    return -1;
}
