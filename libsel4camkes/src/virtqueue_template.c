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

#include <camkes/virtqueue.h>
#include <camkes/virtqueue_template.h>

camkes_virtqueue_channel_t camkes_virtqueue_channels[MAX_CAMKES_VIRTQUEUE_ID + 1];
int num_registered_virtqueue_channels = 0;

int camkes_virtqueue_channel_register(int virtqueue_id, size_t size, volatile void *buf, notify_fn notify, virtqueue_role_t role)
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
    vq_channel->notify = notify;
    vq_channel->role = role;
    vq_channel->buffer_allocated = 0;
    num_registered_virtqueue_channels++;
    return 0;
}
