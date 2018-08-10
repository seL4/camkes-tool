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

int camkes_virtqueue_buffer_alloc(virtqueue_driver_t *virtqueue, volatile void **buffer, size_t alloc_size) {
    /* Check that the virtqueue or buffer pointer is not NULL */
    if(virtqueue == NULL) {
        return -1;
    }
    if(buffer == NULL) {
        return -1;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(virtqueue->data->cookie == NULL) {
        return -1;
    }
    camkes_virtqueue_channel_t *channel = (camkes_virtqueue_channel_t *)virtqueue->data->cookie;
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


void camkes_virtqueue_buffer_free(virtqueue_driver_t *virtqueue, volatile void *buffer) {
    /* Check that the virtqueue or buffer pointer is not NULL */
    if(virtqueue == NULL) {
        return;
    }
    if(buffer == NULL) {
        return;
    }
    /* Check that the cookie pointer is not NULL. Required to get our buffer */
    if(virtqueue->data->cookie == NULL) {
        return;
    }
    camkes_virtqueue_channel_t *channel = (camkes_virtqueue_channel_t *)virtqueue->data->cookie;
    /* We prevent the buffer from being allocated a second time */
    if(!channel->buffer_allocated) {
        ZF_LOGE("CAmkES Buffer %p has already been free'd\n", buffer);
        return;
    }
    channel->buffer_allocated = 0;
}

static camkes_virtqueue_channel_t * get_virtqueue_channel(virtqueue_role_t role, unsigned int camkes_virtqueue_id) {
    /* Check that the virtqueue id is in a valid range */
    if(camkes_virtqueue_id > MAX_CAMKES_VIRTQUEUE_ID) {
        return NULL;
    }
    /* Return error if the given virtqueue channel hasn't been initialized */
    if(camkes_virtqueue_channels[camkes_virtqueue_id].role == VIRTQUEUE_UNASSIGNED) {
        return NULL;
    }
    camkes_virtqueue_channel_t *channel = &camkes_virtqueue_channels[camkes_virtqueue_id];
    /* Check that the buffer is not NULL */
    if(channel->channel_buffer == NULL) {
        return NULL;
    }

    if (channel->role != role) {
        ZF_LOGE("role provided does not match role trying to bind to.");
        return NULL;
    }

    return channel;
}


int camkes_virtqueue_driver_init(virtqueue_driver_t **driver, unsigned int camkes_virtqueue_id) {
    if (driver == NULL) {
        return -1;
    }

    camkes_virtqueue_channel_t *channel = get_virtqueue_channel(VIRTQUEUE_DRIVER, camkes_virtqueue_id);
    if (channel == NULL) {
        ZF_LOGE("Failed to get channel");
        return -1;
    }
    ps_malloc_ops_t malloc_ops;
    ps_new_stdlib_malloc_ops(&malloc_ops);

    int res = virtqueue_driver_init(driver, channel->notify, (virtqueue_header_t *)channel->channel_buffer,
        (void *)channel, &malloc_ops);
    if(res) {
        ZF_LOGE("Failed init");
        return -1;
    }

    (*driver)->data->buffer = channel->channel_buffer + sizeof(virtqueue_header_t);
    return 0;

}
int camkes_virtqueue_device_init(virtqueue_device_t **device, unsigned int camkes_virtqueue_id) {
    if (device == NULL) {
        return -1;
    }

    camkes_virtqueue_channel_t *channel = get_virtqueue_channel(VIRTQUEUE_DEVICE, camkes_virtqueue_id);
    if (channel == NULL) {
        ZF_LOGE("Failed to get channel");
        return -1;
    }

    ps_malloc_ops_t malloc_ops;
    ps_new_stdlib_malloc_ops(&malloc_ops);

    int res = virtqueue_device_init(device, channel->notify, (virtqueue_header_t *)channel->channel_buffer,
        (void *)channel, &malloc_ops);
    if(res) {
        ZF_LOGE("Failed init");
        return -1;
    }
    (*device)->data->buffer = channel->channel_buffer + sizeof(virtqueue_header_t);
    return 0;
}

int camkes_virtqueue_driver_free(virtqueue_driver_t *driver) {
    ps_malloc_ops_t malloc_ops;
    ps_new_stdlib_malloc_ops(&malloc_ops);
    return virtqueue_driver_free(driver, &malloc_ops);
}

int camkes_virtqueue_device_free(virtqueue_device_t *device) {
    ps_malloc_ops_t malloc_ops;
    ps_new_stdlib_malloc_ops(&malloc_ops);
    return virtqueue_device_free(device, &malloc_ops);
}

int camkes_virtqueue_channel_num(void) {
    /* Return number of registered virtqueue channels */
    return num_registered_virtqueue_channels;
}
