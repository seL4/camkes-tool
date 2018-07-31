/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

// #define ZF_LOG_LEVEL ZF_LOG_DEBUG

#include <utils/util.h>

#include <sync/mutex.h>

#include <camkes/sync.h>
#include <camkes/allocator.h>
#include <camkes/tls.h>

int camkes_mutex_new(camkes_mutex_allocator *allocator, void **mutex)
{
    ZF_LOGD("called by %p",
            camkes_get_tls()->thread_index);
    return allocator->alloc(allocator->cookie, mutex);
}

int camkes_mutex_lock(void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    return sync_mutex_lock(mutex);
}

int camkes_mutex_unlock(void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    return sync_mutex_unlock(mutex);
}

int camkes_mutex_free(camkes_mutex_allocator *allocator, void *mutex)
{
    ZF_LOGD("called by %p on cap %d",
            camkes_get_tls()->thread_index,
            ((sync_mutex_t *)mutex)->notification.cptr);
    return allocator->free(allocator->cookie, mutex);
}

/* Allocates a mutex using camkes_alloc */
static int alloc_mutex(void * cookie, void **mutex)
{
    if (mutex == NULL) {
        ZF_LOGE("No return address provided");
        return -1;
    }

    /* The arguments to camkes_alloc need to match what arguements were given when the objects were added
     * to the allocator by the camkes runtime. It treates notification objects as 0 sized and with Read
     * Write cap rights. */
    seL4_CPtr cap = camkes_alloc(seL4_NotificationObject, 0, seL4_CanRead.words[0] | seL4_CanWrite.words[0]);
    if (cap == seL4_CapNull) {
        ZF_LOGE("Failed to allocate notification object");
    }

    /* Allocate underlying mutex struct. We use the implementation from libsel4sync */
    sync_mutex_t *mtx = calloc(1, sizeof(mtx[0]));
    if (mtx == NULL) {
        ZF_LOGE("ENOMEM allocating malloc");
        camkes_free(cap);
        return -1;
    }

    /* Init the mutex. */
    int res = sync_mutex_init(mtx, cap);
    if (res) {
        ZF_LOGE("sync_mutex_init failed");
        free(mtx);
        camkes_free(cap);
        return -1;
    }
    *mutex = mtx;
    return 0;
}

/* Free a mutex back to the camkes allocator */
static int free_mutex(void * cookie, void *mutex)
{
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
int init_default_allocator(camkes_mutex_allocator *allocator)
{
    if (allocator == NULL) {
        ZF_LOGE("Trying to init a NULL allocator");
        return -1;
    }

    camkes_mutex_allocator a = {
        .alloc = alloc_mutex,
        .free = free_mutex,
        .cookie = NULL
    };

    *allocator = a;
    return 0;
}


/**
 * Allocates the allocator struct and then calls init_default_allocator
 */
int init_default_allocator_heap(camkes_mutex_allocator **allocator)
{
    if (allocator == NULL) {
        ZF_LOGE("Trying to init a NULL allocator");
        return -1;
    }
    *allocator = malloc(sizeof(camkes_mutex_allocator));
    if (*allocator == NULL) {
        ZF_LOGE("Trying to init a NULL allocator");
        return -1;
    }
    return init_default_allocator(*allocator);

}

