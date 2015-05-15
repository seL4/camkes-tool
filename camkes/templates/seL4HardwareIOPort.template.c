/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <assert.h>
#include <camkes/error.h>
#include <stdio.h>
#include <stdint.h>
#include <sel4/sel4.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set instance = me.to_instance.name -*/
/*- set interface = me.to_interface.name -*/

/*- set ioport = [] -*/
/*- set p = Perspective(to_interface=me.to_interface.name) -*/
/*- set attr = configuration[me.to_instance.name].get(p['hardware_attribute']) -*/
/*- set port_range = [] -*/
/*- if attr is not none -*/
    /*- set start, end = attr.strip('"').split(':') -*/
    /*- set start = int(start, 0) -*/
    /*- set end = int(end, 0) -*/
    /*- do port_range.extend([start, end]) -*/
    /*- do ioport.append(alloc('ioport', seL4_IA32_IOPort)) -*/
    /*- do cap_space.cnode[ioport[0]].set_ports(range(start, end + 1)) -*/
    int /*? me.from_interface.name ?*/_in_range(unsigned int port) {
        return port >= /*? start ?*/ && port < /*? end ?*/;
    }
/*- endif -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.to_interface.name -*/
/*- include 'error-handler.c' -*/

uint8_t /*? me.from_interface.name ?*/_in8(uint16_t port)
{
	seL4_IA32_IOPort_In8_t reply = seL4_IA32_IOPort_In8(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to read from IO port",
            .syscall = IA32IOPortIn8,
            .error = reply.error,
        }), ({
            return 0;
        }));

	return reply.result;
}

uint8_t /*? me.from_interface.name ?*/_in8_offset(uint16_t offset)
{
    return /*? me.from_interface.name ?*/_in8(/*? port_range[0] ?*/ + offset);
}

uint16_t /*? me.from_interface.name ?*/_in16(uint16_t port)
{
	seL4_IA32_IOPort_In16_t reply = seL4_IA32_IOPort_In16(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to read from IO port",
            .syscall = IA32IOPortIn16,
            .error = reply.error,
        }), ({
            return 0;
        }));

	return reply.result;
}

uint16_t /*? me.from_interface.name ?*/_in16_offset(uint16_t offset)
{
    return /*? me.from_interface.name ?*/_in16(/*? port_range[0] ?*/ + offset);
}

uint32_t /*? me.from_interface.name ?*/_in32(uint16_t port)
{
	seL4_IA32_IOPort_In32_t reply = seL4_IA32_IOPort_In32(/*? ioport[0] ?*/, port);

    ERR_IF(reply.error != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to read from IO port",
            .syscall = IA32IOPortIn32,
            .error = reply.error,
        }), ({
            return 0;
        }));

	return reply.result;
}

uint32_t /*? me.from_interface.name ?*/_in32_offset(uint16_t offset)
{
    return /*? me.from_interface.name ?*/_in32(/*? port_range[0] ?*/ + offset);
}

void /*? me.from_interface.name ?*/_out8(uint16_t port, uint8_t value)
{
	int reply = seL4_IA32_IOPort_Out8(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to write to IO port",
            .syscall = IA32IOPortOut8,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.from_interface.name ?*/_out8_offset(uint16_t offset, uint8_t value)
{
    /*? me.from_interface.name ?*/_out8(/*? port_range[0] ?*/ + offset, value);
}

void /*? me.from_interface.name ?*/_out16(uint16_t port, uint16_t value)
{
	int reply = seL4_IA32_IOPort_Out16(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to write to IO port",
            .syscall = IA32IOPortOut16,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.from_interface.name ?*/_out16_offset(uint16_t offset, uint16_t value)
{
    /*? me.from_interface.name ?*/_out16(/*? port_range[0] ?*/ + offset, value);
}

void /*? me.from_interface.name ?*/_out32(uint16_t port, uint32_t value)
{
	int reply = seL4_IA32_IOPort_Out32(/*? ioport[0] ?*/, port, value);

    ERR_IF(reply != 0, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "failed to write to IO port",
            .syscall = IA32IOPortOut32,
            .error = reply,
        }), ({
            return;
        }));
}

void /*? me.from_interface.name ?*/_out32_offset(uint16_t offset, uint32_t value)
{
    /*? me.from_interface.name ?*/_out32(/*? port_range[0] ?*/ + offset, value);
}

