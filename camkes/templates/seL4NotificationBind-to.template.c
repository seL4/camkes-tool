/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <sel4/sel4.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set notification = alloc('notification', seL4_NotificationObject, read=True, write=True) -*/

seL4_CPtr /*? me.interface.name ?*/_notification(void) {
    return /*? notification ?*/;
}
