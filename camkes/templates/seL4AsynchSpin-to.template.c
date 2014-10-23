/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*? macros.show_includes(me.to_instance.type.includes) ?*/
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdlib.h>

/*- set aep = alloc('aep', seL4AsyncEndpointObject, read=True) -*/

#define MAX_CALLBACKS 10
static void (*volatile callbacks[MAX_CALLBACKS])(void*);
static void *callback_args[MAX_CALLBACKS];
static unsigned int pending;

int /*? me.to_interface.name ?*/__run(void) {
    while (true) {
        bool handled = false;

        (void)seL4_Wait(/*? aep ?*/, NULL);

        if (!handled) {
            for (int i = 0; i < sizeof(callbacks) / sizeof(callbacks[0]); i++) {
                void (*cb)(void*) = callbacks[i];
                if (cb != NULL) {
                    callbacks[i] = NULL;
                    cb(callback_args[i]);
                    handled = true;
                    break;
                }
            }
        }

        if (!handled) {
            pending = 1;
        }
    }
}

int /*? me.to_interface.name ?*/_poll(void) {
    return __sync_val_compare_and_swap(&pending, 1, 0);
}

void /*? me.to_interface.name ?*/_wait(void) {
    while (!/*? me.to_interface.name ?*/_poll());
}

int /*? me.to_interface.name ?*/_reg_callback(void (*callback)(void*), void *arg) {
    for (int i = 0; i < sizeof(callbacks) / sizeof(callbacks[0]); i++) {
        if (__sync_bool_compare_and_swap(&callbacks[i], NULL, callback)) {
            callback_args[i] = arg;
            return 0;
        }
    }
    return -1;
}
