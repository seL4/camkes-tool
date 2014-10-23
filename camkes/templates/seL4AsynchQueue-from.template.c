/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <sel4/sel4.h>
#include <utils/util.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, write=True) -*/

char /*? me.from_interface.name ?*/_data[ROUND_UP_UNSAFE(sizeof(int), PAGE_SIZE_4K)]
    VISIBLE;
volatile int *counter = (volatile int*)/*? me.from_interface.name ?*/_data;
/*? register_shared_variable('%s_data' % me.name, '%s_data' % me.from_interface.name) ?*/

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

void /*? me.from_interface.name ?*/_emit_underlying(void) {
    __sync_fetch_and_add(counter, 1);
    seL4_Notify(/*? aep ?*/, /* ignored */ 0);
}
