/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// #define ZF_LOG_LEVEL ZF_LOG_DEBUG

#include <utils/util.h>

#include <sync/mutex.h>

#include <camkes/sync.h>
#include <camkes/allocator.h>
#include <camkes/tls.h>

/* Allocates a mutex using camkes_alloc */
static void *camkes_mutex_new(void)
{
    ZF_LOGD("called by %p",
            camkes_get_tls()->thread_index);

    /* The arguments to camkes_alloc need to match what arguements were given when the objects were added
     * to the allocator by the camkes runtime. It treates notification objects as 0 sized and with Read
     * Write cap rights. */
    seL4_CPtr cap = camkes_alloc(seL4_NotificationObject, 0, seL4_CanRead.words[0] | seL4_CanWrite.words[0]);
    if (cap == seL4_CapNull) {
        ZF_LOGE("Failed to allocate notification object");
        return NULL;
    }

    /* Allocate underlying mutex struct. We use the implementation from libsel4sync */
    sync_mutex_t *mtx = calloc(1, sizeof(mtx[0]));
    if (mtx == NULL) {
        ZF_LOGE("ENOMEM allocating malloc");
        camkes_free(cap);
        return NULL;
    }

    /* Init the mutex. */
    int res = sync_mutex_init(mtx, cap);
    if (res) {
        ZF_LOGE("sync_mutex_init failed");
        free(mtx);
        camkes_free(cap);
        return NULL;
    }
    return mtx;
}

static int camkes_mutex_lock(void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    return sync_mutex_lock(mutex);
}

static int camkes_mutex_unlock(void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    return sync_mutex_unlock(mutex);
}

/* Free a mutex back to the camkes allocator */
static int camkes_mutex_free(void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    /* There isn't a sync_mutex_free for a preallocated mutex.
     * We just release the Cap the notification object to the camkes allocator.
     */
    sync_mutex_t *mtx = mutex;
    camkes_free(mtx->notification.cptr);
    free(mtx);
    return 0;
}

/**
 * Populates function pointers. Takes a preallocated struct.
 */
int init_camkes_mutex_ops(ps_mutex_ops_t *mutex_ops)
{
    if (mutex_ops == NULL) {
        ZF_LOGE("Trying to init a NULL mutex_ops");
        return -1;
    }
    ps_mutex_ops_t mutex_ops_interface = {
        .mutex_new = camkes_mutex_new,
        .mutex_lock = camkes_mutex_lock,
        .mutex_unlock = camkes_mutex_unlock,
        .mutex_destroy = camkes_mutex_free,
    };


    *mutex_ops = mutex_ops_interface;
    return 0;
}


/**
 * Allocates the allocator struct and then calls init_default_allocator
 */
int init_camkes_mutex_ops_heap(ps_mutex_ops_t **mutex_ops)
{
    if (mutex_ops == NULL) {
        ZF_LOGE("Trying to init a NULL mutex_ops");
        return -1;
    }
    *mutex_ops = malloc(sizeof(ps_mutex_ops_t));
    if (*mutex_ops == NULL) {
        ZF_LOGE("Trying to init a NULL allocator");
        return -1;
    }
    return init_camkes_mutex_ops(*mutex_ops);

}

