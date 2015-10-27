/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <sel4/sel4.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, write=True) -*/
/*- set badge = configuration[me.instance.name].get('%s_attributes' % me.interface.name) -*/
/*- if badge is not none -*/
    /*- set badge = badge.strip('"') -*/
    /*- do cap_space.cnode[aep].set_badge(int(badge, 0)) -*/
/*- endif -*/

int /*? me.interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

void /*? me.interface.name ?*/_emit_underlying(void) {
    seL4_Notify(/*? aep ?*/, /* ignored */ 0);
}
