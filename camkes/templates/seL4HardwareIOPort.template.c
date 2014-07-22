/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*- import 'macros.jinja' as macros -*/

#include <assert.h>
#include <stdio.h>
#include <sel4/sel4.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set ioport = [] -*/
/*- set p = Perspective(to_interface=me.to_interface.name) -*/
/*- set attr = p['hardware_attribute'] -*/
/*- for i in configuration.settings -*/
    /*- if attr == i.attribute and i.instance == me.to_instance.name -*/
        /*- set start, end = i.value.strip('"').split(':') -*/
        /*- set start = int(start, 16) -*/
        /*- set end = int(end, 16) -*/
        /*- do ioport.append(alloc('ioport', seL4_IA32_IOPort)) -*/
        /*- do cap_space.cnode[ioport[0]].set_ports(range(start, end + 1)) -*/
        /*- break -*/
    /*- endif -*/
/*- endfor -*/

uint8_t /*? me.from_interface.name ?*/_in8(uint16_t port)
{
	seL4_IA32_IOPort_In8_t reply = seL4_IA32_IOPort_In8(/*? ioport[0] ?*/, port);

	if (reply.error != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply.error);
		assert(reply.error == 0);
	}

	return reply.result;
}

uint16_t /*? me.from_interface.name ?*/_in16(uint16_t port)
{
	seL4_IA32_IOPort_In16_t reply = seL4_IA32_IOPort_In16(/*? ioport[0] ?*/, port);

	if (reply.error != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply.error);
		assert(reply.error == 0);
	}

	return reply.result;
}

uint32_t /*? me.from_interface.name ?*/_in32(uint16_t port)
{
	seL4_IA32_IOPort_In32_t reply = seL4_IA32_IOPort_In32(/*? ioport[0] ?*/, port);

	if (reply.error != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply.error);
		assert(reply.error == 0);
	}

	return reply.result;
}

void /*? me.from_interface.name ?*/_out8(uint16_t port, uint8_t value)
{
	int reply = seL4_IA32_IOPort_Out8(/*? ioport[0] ?*/, port, value);

	if (reply != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply);
		assert(reply == 0);
	}
}

void /*? me.from_interface.name ?*/_out16(uint16_t port, uint16_t value)
{
	int reply = seL4_IA32_IOPort_Out16(/*? ioport[0] ?*/, port, value);

	if (reply != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply);
		assert(reply == 0);
	}
}

void /*? me.from_interface.name ?*/_out32(uint16_t port, uint32_t value)
{
	int reply = seL4_IA32_IOPort_Out32(/*? ioport[0] ?*/, port, value);

	if (reply != 0) {
		fprintf(stderr, "Syscall failed in \"%s\" error %d!\n", __func__, reply);
		assert(reply == 0);
	}
}
