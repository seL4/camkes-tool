/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <sel4/sel4.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, write=True) -*/
/*- set badge = configuration[me.from_instance.name].get('%s_attributes' % me.from_interface.name) -*/
/*- if badge is not none -*/
    /*- set badge = badge.strip('"') -*/
    /*- do cap_space.cnode[aep].set_badge(int(badge, 0)) -*/
/*- endif -*/

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

void /*? me.from_interface.name ?*/_emit_underlying(void) {
    seL4_Notify(/*? aep ?*/, /* ignored */ 0);
}
