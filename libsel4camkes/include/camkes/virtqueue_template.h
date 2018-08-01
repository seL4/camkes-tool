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

#include <virtqueue.h>
#include <camkes/virtqueue.h>

/* Registers a virtqueue channel. This is expected to be called from a template.
 * @param virtqueue_id A unique id (< MAX_CAMKES_VIRTQUEUE_ID) to register the
 * channel with
 * @param size Size of the virtqueue buffer shared memory region
 * @param buf A pointer to the shared memory region used to create a virtqueue
 * @param notify A function pointer that performs a signal on the virtqueue
 * @param role The components role over the virtqueue channel (DEVICE or DRIVER)
 * @return Positive 0 on success, -1 on error
 */
int camkes_register_virtqueue_channel(int virtqueue_id, size_t size, volatile void *buf, notify_fn_t notify, virtqueue_role_t role);
