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

#include <platsupport/sync/sync.h>

/* Initialises a ps_mutex_ops_t interface that uses camkes/alloc.h to allocate mutexes from a
 * camkes seL4Notification pool. The maximum number of mutexes must be defined at build time.
 * If a mutex is freed, it can be allocated again.
 */
int init_camkes_mutex_ops(ps_mutex_ops_t *mutex_ops);

/* Initialises the ps_mutex_ops_t but will call malloc internally to do this. */
int init_camkes_mutex_ops_heap(ps_mutex_ops_t **mutex_ops);

