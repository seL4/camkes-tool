/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*- import 'helpers/error.c' as error with context -*/

#include <assert.h>
#include <camkes/error.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <sel4/sel4.h>
#include <camkes/io.h>
#include <utils/attribute.h>
#include <platsupport/io.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set ioport = [] -*/
/*- set attr = configuration[me.parent.to_instance.name].get('%s_attributes' % me.parent.to_interface.name) -*/
/*- set port_range = [] -*/
/*- if attr is not none -*/
    /*- set start, end = attr.strip('"').split(':') -*/
    /*- set start = int(start, 0) -*/
    /*- set end = int(end, 0) -*/
    /*- do port_range.extend([start, end]) -*/
    /*- do ioport.append(alloc('ioport', seL4_IA32_IOPort, start_port=start, end_port=end + 1)) -*/
    int /*? me.interface.name ?*/_in_range(unsigned port) {
        return port >= /*? start ?*/ && port <= /*? end ?*/;
    }
/*- endif -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.parent.to_interface.name -*/
/*? error.make_error_handler(me.interface.name, error_handler) ?*/

static char *interface_name = "/*? me.parent.to_interface ?*/";

/* Expose the IO port region */
static ioport_region_t /*? me.interface.name ?*/_region = {
    .start = /*? start ?*/,
    .end = /*? end ?*/,
    .cap = /*? ioport[0] ?*/,
    .error_handler = /*? error_handler ?*/,
    .interface_name = &interface_name,
};
USED SECTION("_ioport_regions")
ioport_region_t * /*? me.interface.name ?*/_region_ptr = &/*? me.interface.name ?*/_region;

static ps_io_port_ops_t ops;

static bool ops_inited = false;

static inline int init_io_port_ops(void)
{
    assert(camkes_io_port_ops(&ops) == 0);
    ops_inited = true;
    return 0;
}

uint8_t /*? me.interface.name ?*/_in8_offset(uint16_t offset)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    uint32_t result = 0;
    int ret = ps_io_port_in(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_8, &result);
    if (ret) {
        return 0;
    }

    return (uint8_t) result;
}

uint16_t /*? me.interface.name ?*/_in16_offset(uint16_t offset)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    uint32_t result = 0;
    int ret = ps_io_port_in(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_16, &result);
    if (ret) {
        return 0;
    }

    return (uint16_t) result;
}

uint32_t /*? me.interface.name ?*/_in32_offset(uint16_t offset)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    uint32_t result = 0;
    int ret = ps_io_port_in(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_32, &result);
    if (ret) {
        return 0;
    }

    return (uint32_t) result;
}

void /*? me.interface.name ?*/_out8_offset(uint16_t offset, uint8_t value)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    /* Ignore the return value */
    ps_io_port_out(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_8, value);
}

void /*? me.interface.name ?*/_out16_offset(uint16_t offset, uint16_t value)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    /* Ignore the return value */
    ps_io_port_out(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_16, value);
}

void /*? me.interface.name ?*/_out32_offset(uint16_t offset, uint32_t value)
{
    if (!ops_inited) {
        init_io_port_ops();
    }

    assert(/*? me.interface.name ?*/_in_range(/*? port_range[0] ?*/ + offset));
    /* Ignore the return value */
    ps_io_port_out(&ops, /*? port_range[0] ?*/ + offset, IOSIZE_32, value);
}
