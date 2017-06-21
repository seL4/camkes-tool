/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <assert.h>
#include <camkes/error.h>
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/

/*- set attr = "%s_attributes" % me.parent.from_interface.name -*/
/*- set irq= [] -*/
/*- set notification_obj = alloc_obj('notification', seL4_NotificationObject) -*/
/*- set notification = alloc_cap('notification', notification_obj, read=True) -*/
/*- set _irq = configuration[me.parent.from_instance.name].get(attr) -*/
/*- if _irq is not none -*/
    /*- set attr_irq, attr_level, attr_trig = _irq.strip('"').split(',') -*/
    /*- set irq_handler = alloc('irq', seL4_IRQControl, number=int(attr_irq, 0), notification=my_cnode[notification]) -*/
    /*- do irq.append((irq_handler, int(attr_level, 0), int(attr_trig, 0))) -*/
/*- endif -*/
/*- set lock = alloc('lock', seL4_NotificationObject, read=True, write=True) -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*- include 'error-handler.c' -*/

#define MAX_CALLBACKS 10

static void (*volatile callbacks[MAX_CALLBACKS])(void*);
static void *callback_args[MAX_CALLBACKS];
static volatile int event_pending;
static volatile int sleepers;

#define CAS __sync_val_compare_and_swap
#define ATOMIC_INCREMENT(ptr) __sync_fetch_and_add((ptr), 1)
#define ATOMIC_DECREMENT(ptr) __sync_fetch_and_sub((ptr), 1)

#define SLEEP() \
    do { \
        ATOMIC_INCREMENT(&sleepers); \
        assert(sleepers > 0); \
        seL4_Wait(/*? lock ?*/, NULL); \
        assert(sleepers > 0); \
        ATOMIC_DECREMENT(&sleepers); \
    } while (0)

#define WAKE() seL4_Signal(/*? lock ?*/)

int /*? me.interface.name ?*/__run(void) {
    /* Set trigger mode */
    seL4_IRQHandler_SetMode(/*? irq[0][0] ?*/, /*? irq[0][1] ?*/, /*? irq[0][2] ?*/);
    while (1) {
        int handled = 0;

        seL4_Wait(/*? notification ?*/, NULL);

        /* First preference: callbacks. */
        if (!handled) {
            for (int i = 0; i < MAX_CALLBACKS; ++i) {
                void (*callback)(void*) = callbacks[i];
                if (callback != NULL) {
                    callbacks[i] = NULL; /* No need for CAS. */
                    callback(callback_args[i]);
                    handled = 1;
                }
            }
        }

        /* There may in fact already be a pending event, but we don't care. */
        event_pending = 1;

        /* Second preference: waiters. */
        if (!handled) {
            if (sleepers > 0) { /* No lock required. */
                WAKE();
                /* Assume one of them will grab it. */
                handled = 1;
            }
        }

        /* Else, leave it for polling. */
    }

    UNREACHABLE();
}

int /*? me.interface.name ?*/_poll(void) {
    return CAS(&event_pending, 1, 0);
}

void /*? me.interface.name ?*/_wait(void) {
    while (!/*? me.interface.name ?*/_poll()) {
        SLEEP();
    }
}

int /*? me.interface.name ?*/_reg_callback(void (*callback)(void*), void *arg) {
    int error;
    for (int i = 0; i < MAX_CALLBACKS; ++i) {
        if (CAS(&callbacks[i], NULL, callback) == NULL) {
            callback_args[i] = arg;
            error = seL4_IRQHandler_Ack(/*? irq[0][0] ?*/);
            ERR_IF(error != 0, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_SYSCALL_FAILED,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "failed to acknowledge IRQ",
                    .syscall = IRQAckIRQ,
                    .error = error,
                }), ({
                    return -1;
                }));
            return 0;
        }
    }
    /* We didn't find an empty slot. */
    return -1;
}
