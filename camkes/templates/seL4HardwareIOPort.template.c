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

#include <assert.h>
#include <camkes/error.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <sel4/sel4.h>

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
/*- set interface = me.interface.name -*/
/*- set error_handler = '%s_error_handler' % me.parent.to_interface.name -*/
/*- include 'error-handler.c' -*/

uint8_t /*? me.interface.name ?*/_in8(uint16_t port)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    seL4_X86_IOPort_In8_t reply = seL4_X86_IOPort_In8(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to read from IO port",
            .syscall = X86IOPortIn8,
            .error = reply.error,
        }), ({
            return 0;
        }));

    return reply.result;
}

uint8_t /*? me.interface.name ?*/_in8_offset(uint16_t offset)
{
    return /*? me.interface.name ?*/_in8(/*? port_range[0] ?*/ + offset);
}

uint16_t /*? me.interface.name ?*/_in16(uint16_t port)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    seL4_X86_IOPort_In16_t reply = seL4_X86_IOPort_In16(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to read from IO port",
            .syscall = X86IOPortIn16,
            .error = reply.error,
        }), ({
            return 0;
        }));

    return reply.result;
}

uint16_t /*? me.interface.name ?*/_in16_offset(uint16_t offset)
{
    return /*? me.interface.name ?*/_in16(/*? port_range[0] ?*/ + offset);
}

uint32_t /*? me.interface.name ?*/_in32(uint16_t port)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    seL4_X86_IOPort_In32_t reply = seL4_X86_IOPort_In32(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to read from IO port",
            .syscall = X86IOPortIn32,
            .error = reply.error,
        }), ({
            return 0;
        }));

    return reply.result;
}

uint32_t /*? me.interface.name ?*/_in32_offset(uint16_t offset)
{
    return /*? me.interface.name ?*/_in32(/*? port_range[0] ?*/ + offset);
}

void /*? me.interface.name ?*/_out8(uint16_t port, uint8_t value)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    int reply = seL4_X86_IOPort_Out8(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to write to IO port",
            .syscall = X86IOPortOut8,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.interface.name ?*/_out8_offset(uint16_t offset, uint8_t value)
{
    /*? me.interface.name ?*/_out8(/*? port_range[0] ?*/ + offset, value);
}

void /*? me.interface.name ?*/_out16(uint16_t port, uint16_t value)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    int reply = seL4_X86_IOPort_Out16(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to write to IO port",
            .syscall = X86IOPortOut16,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.interface.name ?*/_out16_offset(uint16_t offset, uint16_t value)
{
    /*? me.interface.name ?*/_out16(/*? port_range[0] ?*/ + offset, value);
}

void /*? me.interface.name ?*/_out32(uint16_t port, uint32_t value)
{
    assert(/*? me.interface.name ?*/_in_range(port));
    int reply = seL4_X86_IOPort_Out32(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.parent.to_instance.name ?*/",
            .interface = "/*? me.parent.to_interface.name ?*/",
            .description = "failed to write to IO port",
            .syscall = X86IOPortOut32,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.interface.name ?*/_out32_offset(uint16_t offset, uint32_t value)
{
    /*? me.interface.name ?*/_out32(/*? port_range[0] ?*/ + offset, value);
}
