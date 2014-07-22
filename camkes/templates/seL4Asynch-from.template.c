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
#include <sel4/sel4.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, write=True) -*/

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

void /*? me.from_interface.name ?*/_emit_underlying(void) {
    seL4_Notify(/*? aep ?*/, /* ignored */ 0);
}
