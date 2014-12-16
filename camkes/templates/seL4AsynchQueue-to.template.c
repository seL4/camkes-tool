/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*# XXX: The functions here are crying out for some model checking. #*/
#include <assert.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.to_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, read=True) -*/

char /*? me.to_interface.name ?*/_data[ROUND_UP_UNSAFE(sizeof(int), PAGE_SIZE_4K)]
    VISIBLE;
volatile int *counter = (volatile int*)/*? me.to_interface.name ?*/_data;
/*? register_shared_variable('%s_data' % me.name, '%s_data' % me.to_interface.name) ?*/

#define MAX_CALLBACKS 10

static void (*volatile callbacks[MAX_CALLBACKS])(void*);
static void *callback_args[MAX_CALLBACKS];
static volatile int pending;

static void accept(void) {
    for (int i = 0; i < sizeof(callbacks) / sizeof(callbacks[0]); i++) {
        void (*callback)(void*) = callbacks[i];
        if (callback != NULL) {
            callbacks[i] = NULL; /* No need for CAS. */
            callback(callback_args[i]);
            return;
        }
    }
    __sync_fetch_and_add(&pending, 1);
}

int /*? me.to_interface.name ?*/__run(void) {
    /* This algorithm is more complicated than may appear necessary in an
     * attempt to cope with N-to-1 connections.
     */
    while (true) {
        while (__sync_sub_and_fetch(counter, 1) >= 0) {
            accept();
        }
        __sync_fetch_and_add(counter, 1);
        (void)seL4_Wait(/*? aep ?*/, NULL);
    }

    assert(!"Unreachable");
}

int /*? me.to_interface.name ?*/_poll(void) {
    /* Algorithm based on libsel4sync/src/sem.c:trywait */
    int value = pending;
    while (value > 0) {
        int old = __sync_val_compare_and_swap(&pending, value, value - 1);
        if (old == value) {
            /* Found an event. */
            return 1;
        }
        /* Someone interferred with our update. */
        value = old;
    }
    /* No event was found. */
    return 0;
}

void /*? me.to_interface.name ?*/_wait(void) {
    while (!/*? me.to_interface.name ?*/_poll());
}

int /*? me.to_interface.name ?*/_reg_callback(void (*callback)(void*), void *arg) {
    for (int i = 0; i < MAX_CALLBACKS; ++i) {
        if (__sync_bool_compare_and_swap(&callbacks[i], NULL, callback)) {
            callback_args[i] = arg;
            return 0;
        }
    }
    /* We didn't find an empty slot. */
    return -1;
}
