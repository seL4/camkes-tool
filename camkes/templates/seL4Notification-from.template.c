/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sel4/sel4.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set notifications = [] -*/
/*- for index in six.moves.range(len(me.parent.to_ends)) -*/
  /*- do notifications.append(alloc('notification_%d' % index, seL4_NotificationObject, write=True)) -*/
/*- endfor -*/

void /*? me.interface.name ?*/_emit_underlying(void) {
    /*- for notification in notifications -*/
    seL4_Signal(/*? notification ?*/);
    /*- endfor -*/
}
