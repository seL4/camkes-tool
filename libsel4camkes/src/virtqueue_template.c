/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/virtqueue.h>
#include <camkes/virtqueue_template.h>

camkes_virtqueue_channel_t camkes_virtqueue_channels[MAX_CAMKES_VIRTQUEUE_ID + 1];
int num_registered_virtqueue_channels = 0;

int camkes_virtqueue_channel_register(int virtqueue_id, const char *interface_name, unsigned queue_len, size_t size,
                                      volatile void *buf, void (*notify)(void),
                                      seL4_CPtr recv_notification, seL4_Word recv_badge, virtqueue_role_t role)
{
    /* Check that the virtqueue_id is in range */
    if (virtqueue_id > MAX_CAMKES_VIRTQUEUE_ID) {
        return -1;
    }
    /* Check that the buffer and notify function are not NULL */
    if (buf == NULL || notify == NULL) {
        return -1;
    }
    /* Initialise the contents of the virtqueue channel */
    camkes_virtqueue_channel_t *vq_channel = &camkes_virtqueue_channels[virtqueue_id];
    vq_channel->channel_buffer = buf;
    vq_channel->channel_buffer_size = size;
    vq_channel->queue_len = queue_len;
    vq_channel->notify = notify;
    vq_channel->recv_notification = recv_notification;
    vq_channel->recv_badge = recv_badge;
    vq_channel->role = role;
    vq_channel->buffer_allocated = 0;
    vq_channel->interface_name = interface_name;
    num_registered_virtqueue_channels++;
    return 0;
}
