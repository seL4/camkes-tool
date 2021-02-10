/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*- import 'helpers/error.c' as error with context -*/

#include <camkes/error.h>
#include <camkes/tls.h>
#include <limits.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdlib.h>
#include <sync/bin_sem_bare.h>
#include <sync/sem-bare.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/* Interface-specific error handling. */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*? error.make_error_handler(me.interface.name, error_handler) ?*/

/*- set id = me.parent.to_ends.index(me) -*/

/*- set ep = alloc('ep_%d' % id, seL4_EndpointObject, read=True) -*/
/*- set handoff = alloc('handoff_%d' % id, seL4_EndpointObject, label=me.instance.name, read=True, write=True) -*/
static volatile int handoff_value;

char to_/*? id ?*/_/*? me.interface.name ?*/_data[ROUND_UP_UNSAFE(sizeof(int), PAGE_SIZE_4K)]
   ALIGN(4096)
   SECTION("align_12bit");
static volatile int *value = (volatile int*)to_/*? id ?*/_/*? me.interface.name ?*/_data;
/*? register_shared_variable('%s_%d_data' % (me.parent.name, id), 'to_%d_%s_data' % (id, me.interface.name), 4096, perm='RW') ?*/

/*- set lock = alloc('lock_%d' % id, seL4_NotificationObject, label=me.instance.name, read=True, write=True) -*/
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
restart:;
        int result UNUSED = sync_sem_bare_wait(/*? ep ?*/, value);
        ERR_IF(result != 0, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_OVERFLOW,
                .instance = "/*? me.instance.name ?*/",
                .interface = "/*? me.interface.name ?*/",
                .description = "waiting on semaphore failed",
            }), ({
                goto restart;
            }));

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
            ERR_IF(handoff_value == INT_MAX, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_OVERFLOW,
                    .instance = "/*? me.instance.name ?*/",
                    .interface = "/*? me.interface.name ?*/",
                    .description = "handoff to internal endpoint not possible due to counter overflow",
                }), ({
                    int result UNUSED = unlock();
                    assert(result == 0);
                    goto restart;
                }));
            sync_sem_bare_post(/*? handoff ?*/, &handoff_value);
        }

        result = unlock();
        assert(result == 0);

        if (cb != NULL) {
            cb(arg);
        }
    }
}

static int poll(void) {
    return sync_sem_bare_trywait(/*? handoff ?*/, &handoff_value) == 0;
}

int /*? me.interface.name ?*/_poll(void) {
    return poll();
}

void /*? me.interface.name ?*/_wait(void) {
#ifndef CONFIG_KERNEL_MCS
    camkes_protect_reply_cap();
#endif
    if (sync_sem_bare_wait(/*? handoff ?*/, &handoff_value) != 0) {
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

    if (poll()) {
        cb(arg);
        return 0;
    }

    if (lock() != 0) {
        return -1;
    }

    if (poll()) {
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
