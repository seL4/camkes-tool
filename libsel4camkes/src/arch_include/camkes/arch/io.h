/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/*
 * Architectural specific implementation of the IO port operations.
 */
int camkes_arch_io_port_in(uint32_t port, int io_size, uint32_t *result);

int camkes_arch_io_port_out(uint32_t port, int io_size, uint32_t val);
