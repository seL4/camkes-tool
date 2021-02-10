/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sel4/sel4.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set notification = alloc('notification', seL4_NotificationObject, write=True) -*/
/*- set badge = configuration[me.instance.name].get('%s_attributes' % me.interface.name) -*/
/*- if badge is not none -*/
    /*- set badge = badge.strip('"') -*/
    /*- do cap_space.cnode[notification].set_badge(int(badge, 0)) -*/
/*- endif -*/

int /*? me.interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

void /*? me.interface.name ?*/_emit_underlying(void) {
    seL4_Signal(/*? notification ?*/);
}
