/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <platsupport/io.h>
#include <stdint.h>
#include <sel4/sel4.h>
#include <camkes/error.h>
#include <utils/attribute.h>

#define IOSIZE_8 1
#define IOSIZE_16 2
#define IOSIZE_32 4

/* Initialise an IO mapper for use with libplatsupport. Returns 0 on success.
 */
int camkes_io_mapper(ps_io_mapper_t *mapper);

/* Initialise an IO port accessor for use with libplatsupport. Returns 0 on
 * success.
 */
int camkes_io_port_ops(ps_io_port_ops_t *ops);

/* Initialise an IO operations object for use with libplatsupport. Returns 0 on
 * success.
 */
int camkes_io_ops(ps_io_ops_t *ops);

/* Initialise a malloc operations object for use with libplatsupport. Returns 0
 * on success.
 */
int camkes_ps_malloc_ops(ps_malloc_ops_t *ops);

/* Initialise a FDT interface object for use with libplatsupport. Returns 0
 * on success.
 */
int camkes_io_fdt(ps_io_fdt_t *io_fdt);

/*
 * This struct describes an IO port region that is allocated by CAmkES.
 *
 * Instances of this struct is intended to be located inside a section in an ELF file.
 */
struct ioport_region {
    uint16_t start;
    uint16_t end;
    seL4_CPtr cap;
    camkes_error_handler_t error_handler;
    char **interface_name;
};
typedef struct ioport_region ioport_region_t;

/**
 * Call registerd hardware modules initialization functions
 *
 * Some connectors register modules to be intialized by this call.
 *
 * Returns 0 on success
 */
int camkes_call_hardware_init_modules(ps_io_ops_t *ops);
