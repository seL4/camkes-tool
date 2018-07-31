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

#include <stdio.h>
#include <camkes/virtqueue.h>
#include <utils/util.h>
#include <platsupport/io.h>

int alloc_camkes_virtqueue_buffer(virtqueue_t *virtqueue, volatile void **buffer, size_t alloc_size) {
    /* Check that the virtqueue or buffer pointer is not NULL */
    if(virtqueue == NULL) {
        return -1;
    }
    if(buffer == NULL) {
        return -1;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(virtqueue->cookie == NULL) {
        return -1;
    }
    virtqueue_channel_t *channel = (virtqueue_channel_t *)virtqueue->cookie;
    /* We prevent the buffer from being allocated a second time */
    if(channel->buffer_allocated) {
        return -1;
    }
    /* Check we have enough memory to satisfy alloc_size */
    if(alloc_size > channel->channel_buffer_size) {
        return -1;
    }
    /* Simply return the channels buffer.
     * Current basic implementation uses a single slot queue */
    *buffer = channel->channel_buffer + sizeof(virtqueue_header_t);
    /* Flag the buffer as allocated */
    channel->buffer_allocated = 1;
    return 0;
}


void free_camkes_virtqueue_buffer(virtqueue_t *virtqueue, void *buffer) {
    /* Check that the virtqueue or buffer pointer is not NULL */
    if(virtqueue == NULL) {
        return;
    }
    if(buffer == NULL) {
        return;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(virtqueue->cookie == NULL) {
        return;
    }
    virtqueue_channel_t *channel = (virtqueue_channel_t *)virtqueue->cookie;
    /* We prevent the buffer from being allocated a second time */
    if(!channel->buffer_allocated) {
        ZF_LOGE("CAmkES Buffer %p has already been free'd\n", buffer);
        return;
    }
    channel->buffer_allocated = 0;
}

int init_camkes_virtqueue(virtqueue_t **virtqueue, unsigned int camkes_virtqueue_id) {
    /* Check that the virtqueue pointer is not NULL */
    if(virtqueue == NULL) {
        return -1;
    }
    /* Check that the virtqueue id is in a valid range */
    if(camkes_virtqueue_id > MAX_CAMKES_VIRTQUEUE_ID) {
        return -1;
    }
    /* Return error if the given virtqueue channel hasn't been initialized */
    if(virtqueue_channels[camkes_virtqueue_id].role == VIRTQUEUE_UNASSIGNED) {
        return -1;
    }
    virtqueue_channel_t *channel = &virtqueue_channels[camkes_virtqueue_id];
    /* Check that the buffer is not NULL */
    if(channel->channel_buffer == NULL) {
        return -1;
    }
    /* Create a virtqueue object for the given camkes virtqueue channel.
     * We pass the channel as our cookie data */
    ps_malloc_ops_t malloc_ops;
    ps_new_stdlib_malloc_ops(&malloc_ops);
    int res = virtqueue_init(virtqueue, channel->notify, channel->role, (virtqueue_header_t *)channel->channel_buffer, 
            (void *)channel, &malloc_ops);
    if(res) {
        return -1;
    }
    /* XXX: Remove for proper implementation. Since we are currently not sharing buffer addresses/offsets  */
    (*virtqueue)->buffer = channel->channel_buffer + sizeof(virtqueue_header_t);
    return 0;
}

int query_num_virtqueue_channels(void) {
    /* Return number of registered virtqueue channels */
    return num_registered_virtqueue_channels;
}
