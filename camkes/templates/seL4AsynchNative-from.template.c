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

/*# This value is completely arbitrary as long as it matches the one in the
 *# template for the other side of this connector.
 #*/
/*- set badge_magic = int('0xbad1dea', 16) -*/

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_NotificationObject, write=True) -*/
/*- do cap_space.cnode[aep].set_badge(badge_magic) -*/

void /*? me.interface.name ?*/_emit_underlying(void) {
    seL4_Notify(/*? aep ?*/, /* ignored */ 0);
}
