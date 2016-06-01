/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <camkes/error.h>
#include <camkes/tls.h>
#include <limits.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/* Interface-specific error handling. */
/*- set interface = me.interface.name -*/
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*- include 'error-handler.c' -*/

/*- set id = me.parent.to_ends.index(me) -*/

/*- set ep = alloc('ep_%d' % id, seL4_EndpointObject, read=True) -*/
/*- set handoff = alloc('handoff_%d' % id, seL4_EndpointObject, read=True, write=True) -*/
static volatile int handoff;

char to_/*? id ?*/_/*? me.interface.name ?*/_data[ROUND_UP_UNSAFE(sizeof(int), PAGE_SIZE_4K)]
    VISIBLE;
static volatile int *value = (volatile int*)to_/*? id ?*/_/*? me.interface.name ?*/_data;
/*? register_shared_variable('%s_%d_data' % (me.parent.name, id), 'to_%d_%s_data' % (id, me.interface.name), 'RW') ?*/

/*- set lock = alloc('lock_%d' % id, seL4_NotificationObject, read=True, write=True) -*/
static volatile int lock_count = 1;

static int lock(void) {
    int result = sync_bin_sem_bare_wait(/*? lock ?*/, &lock_count);
    __sync_synchronize();
    return result;
}

static int unlock(void) {
    __sync_synchronize();
    return sync_bin_sem_bare_post(/*? lock ?*/, &lock_count);
}

static void (*volatile callback)(void*);
static void *callback_arg;

int /*? me.interface.name ?*/__run(void) {
    while (true) {
restart:
        seL4_Wait(/*? ep ?*/, NULL);

        if (lock() != 0) {
            ERR(/*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_OVERFLOW,
                    .instance = "/*? me.instance.name ?*/",
                    .interface = "/*? me.interface.name ?*/",
                    .description = "lock acquisition failed due to too many outstanding lock holders",
                }), ({
                    goto restart;
                }));
        }

        void (*cb)(void*) = callback;
        callback = NULL;
        void *arg = callback_arg;

        if (cb == NULL) {
            ERR_IF(handoff == INT_MAX, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_OVERFLOW,
                    .instance = "/*? me.instance.name ?*/",
                    .interface = "/*? me.interface.name ?*/",
                    .description = "handoff to internal endpoint not possible due to counter overflow",
                }), ({
                    int result UNUSED = unlock();
                    assert(result == 0);
                    goto restart;
                }));
            sync_sem_bare_post(/*? handoff ?*/, &handoff);
        }

        int result UNUSED = unlock();
        assert(result == 0);

        if (cb != NULL) {
            cb(arg);
        }
    }
}

int /*? me.interface.name ?*/_poll(void) {
    return sync_sem_bare_trywait(/*? handoff ?*/, &handoff) == 0;
}

void /*? me.interface.name ?*/_wait(void) {
    camkes_protect_reply_cap();
    if (sync_sem_bare_wait(/*? handoff ?*/, &handoff) != 0) {
        ERR(/*? error_handler ?*/, ((camkes_error_t){
                .type = CE_OVERFLOW,
                .instance = "/*? me.instance.name ?*/",
                .interface = "/*? me.interface.name ?*/",
                .description = "wait failed due to future counter overflow",
            }), ({
                return;
            }));
    }
}

int /*? me.interface.name ?*/_reg_callback(void (*cb)(void*), void *arg) {

    if (sync_sem_bare_trywait(/*? handoff ?*/, &handoff) == 0) {
        cb(arg);
        return 0;
    }

    if (lock() != 0) {
        ERR(/*? error_handler ?*/, ((camkes_error_t){
                .type = CE_OVERFLOW,
                .instance = "/*? me.instance.name ?*/",
                .interface = "/*? me.interface.name ?*/",
                .description = "lock acquisition failed due to too many outstanding lock holders",
            }), ({
                return -1;
            }));
    }

    if (sync_sem_bare_trywait(/*? handoff ?*/, &handoff) == 0) {
        int result UNUSED = unlock();
        assert(result == 0);
        cb(arg);
        return 0;

    } else if (callback != NULL) {
        int result UNUSED = unlock();
        assert(result == 0);
        return -1;

    } else {
        callback = cb;
        callback_arg = arg;
        int result UNUSED = unlock();
        assert(result == 0);
        return 0;
    }
}
