/*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <camkes/arch/io.h>

int camkes_arch_io_port_in(uint32_t port, int io_size, uint32_t *result)
{
    /* RISCV does not support IO ports */
    return -1;
}

int camkes_arch_io_port_out(uint32_t port, int io_size, uint32_t val)
{
    /* RISCV does not support IO ports */
    return -1;
}
