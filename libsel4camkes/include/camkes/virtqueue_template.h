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
 * @param recv_notification Capability to notification that can receive events from other end
 * @param recv_badge Badge value for events received on the notification
 * @param role The components role over the virtqueue channel (DEVICE or DRIVER)
 * @return Positive 0 on success, -1 on error
 */
int camkes_virtqueue_channel_register(int virtqueue_id, const char *interface_name, unsigned queue_len, size_t size,
									  volatile void *buf, void (*notify)(void),
                                      seL4_CPtr recv_notification, seL4_Word recv_badge, virtqueue_role_t role);
