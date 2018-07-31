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

#pragma once

/* This file defines a simple mutex interface that is intended
 * to be backed by a notification_pool implemented by the Camkes runtime.
 * It doesn't use static inline functions like other libsel4* interfaces
 * in order to allow this interface to be used over a FFI.
 */

/* Allocates a mutex. Returns -1 on failure, 0 on success */
typedef int (*alloc_mutex_fn)(void * cookie, void **mutex);
/* Frees a mutex. Returns -1 on failure, 0 on success */
typedef int (*free_mutex_fn)(void * cookie, void *mutex);

/* Interface struct for allocating mutexs */
typedef struct {
	void * cookie;
	alloc_mutex_fn alloc;
	free_mutex_fn free;
} camkes_mutex_allocator;

/* Creates a new mutex from the allocator */
int camkes_mutex_new(camkes_mutex_allocator *allocator, void **mutex);

/* Acquire mutex. Undefined behavior if caller already holds mutex. */
int camkes_mutex_lock(void *mutex);

/* Release mutex. Undefined behavior if caller tries to release mutex they do not hold. */
int camkes_mutex_unlock(void *mutex);

/* Frees a mutex */
int camkes_mutex_free(camkes_mutex_allocator *allocator, void *mutex);

/* Initialises a default allocator that uses camkes/alloc.h to allocate mutexes from a
 * camkes seL4Notification pool. The maximum number of mutexes must be defined at build time.
 * If a mutex is freed, it can be allocated again.
 */
int init_default_allocator(camkes_mutex_allocator *allocator);

/* Initialises the default allocator but will call malloc internally to do this. */
int init_default_allocator_heap(camkes_mutex_allocator **allocator);

