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
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <stdlib.h>

/*# This value is completely arbitrary as long as it matches the one in the
 *# template for the other side of this connector.
 #*/
/*- set badge_magic = int('0xbad1dea', 16) -*/

/*? macros.show_includes(me.to_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, read=True) -*/
/*- do cap_space.cnode[aep].set_badge(badge_magic) -*/

int /*? me.to_interface.name ?*/__run(void) {
    return 0;
}

/*- set type = 'seL4_Word' -*/
/*- set name = 'badge' -*/
/*- set threads = [1] + map(lambda('x: x + 2'), range(len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.emits + me.to_instance.type.consumes + me.to_instance.type.dataports))) -*/
/*- set array = False -*/
/*- include "thread_local.c" -*/

int /*? me.to_interface.name ?*/_poll(void) {
    seL4_Word *badge = get_badge();
    seL4_Poll(/*? aep ?*/, badge);
    return *badge == /*? badge_magic ?*/;
}

void /*? me.to_interface.name ?*/_wait(void) {
    seL4_Wait(/*? aep ?*/, NULL);
}
