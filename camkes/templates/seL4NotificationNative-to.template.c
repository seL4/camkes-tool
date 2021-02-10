/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <stdlib.h>

/*# This value is completely arbitrary as long as it matches the one in the
 *# template for the other side of this connector.
 #*/
/*- set badge_magic = int('0xbad1dea', 16) -*/

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set notification = alloc('notification', seL4_NotificationObject, read=True) -*/
/*- do cap_space.cnode[notification].set_badge(badge_magic) -*/

int /*? me.interface.name ?*/__run(void) {
    return 0;
}

int /*? me.interface.name ?*/_poll(void) {
    seL4_Word badge = 0;
    seL4_Poll(/*? notification ?*/, &badge);
    return badge == /*? badge_magic ?*/;
}

void /*? me.interface.name ?*/_wait(void) {
    seL4_Wait(/*? notification ?*/, NULL);
}
