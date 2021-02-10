/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sel4/sel4.h>

/*# This value is completely arbitrary as long as it matches the one in the
 *# template for the other side of this connector.
 #*/
/*- set badge_magic = int('0xbad1dea', 16) -*/

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set notification = alloc('notification', seL4_NotificationObject, write=True) -*/
/*- do cap_space.cnode[notification].set_badge(badge_magic) -*/

void /*? me.interface.name ?*/_emit_underlying(void) {
    seL4_Signal(/*? notification ?*/);
}
