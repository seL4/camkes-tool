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
#include <camkes/buffqueue.h>

int alloc_camkes_buffqueue_buffer(buffqueue_t *buffqueue, volatile void **buffer, size_t alloc_size) {
    /* Check that the buffqueue or buffer pointer is not NULL */
    if(buffqueue == NULL) {
        return -1;
    }
    if(buffer == NULL) {
        return -1;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(buffqueue->cookie == NULL) {
        return -1;
    }
    buffqueue_channel_t *channel = (buffqueue_channel_t *)buffqueue->cookie;
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
    *buffer = channel->channel_buffer + sizeof(buffqueue_header_t);
    /* Flag the buffer as allocated */
    channel->buffer_allocated = 1;
    return 0;
}


void free_camkes_buffqueue_buffer(buffqueue_t *buffqueue, void *buffer) {
    /* Check that the buffqueue or buffer pointer is not NULL */
    if(buffqueue == NULL) {
        return;
    }
    if(buffer == NULL) {
        return;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(buffqueue->cookie == NULL) {
        return;
    }
    buffqueue_channel_t *channel = (buffqueue_channel_t *)buffqueue->cookie;
    /* We prevent the buffer from being allocated a second time */
    if(!channel->buffer_allocated) {
        return;
    }
    channel->buffer_allocated = 0;
}

int init_camkes_buffqueue(buffqueue_t **buffqueue, unsigned int camkes_buffqueue_id) {
    /* Check that the buffqueue pointer is not NULL */
    if(buffqueue == NULL) {
        return -1;
    }
    /* Check that the buffqueue id is in a valid range */
    if(camkes_buffqueue_id > MAX_CAMKES_BUFFQUEUE_ID) {
        return -1;
    }
    /* Return error if the given buffqueue channel hasn't been initialized */
    if(buffqueue_channels[camkes_buffqueue_id].role == BUFFQUEUE_UNASSIGNED) {
        return -1;
    }
    buffqueue_channel_t *channel = &buffqueue_channels[camkes_buffqueue_id];
    /* Check that the buffer is not NULL */
    if(channel->channel_buffer == NULL) {
        return -1;
    }
    /* Create a buffqueue object for the given camkes buffqueue channel.
     * We pass the channel as our cookie data */
    int res = buffqueue_init(buffqueue, channel->notify, channel->role, (buffqueue_header_t *)channel->channel_buffer, (void *)channel);
    if(res) {
        return -1;
    }
    /* XXX: Remove for proper implementation. Since we are currently not sharing buffer addresses/offsets  */
    (*buffqueue)->buffer = channel->channel_buffer + sizeof(buffqueue_header_t);
    return 0;
}

int query_num_buffqueue_channels(void) {
    /* Return number of registered buffqueue channels */
    return num_registered_buffqueue_channels;
}
