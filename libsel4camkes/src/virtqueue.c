/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdio.h>
#include <string.h>
#include <camkes/virtqueue.h>
#include <utils/util.h>
#include <platsupport/io.h>

#include "virtqueue_common.h"

#define BLOCK_SIZE 128
#define IDX_TO_OFFSET(block_size, idx) (block_size * idx)
#define OFFSET_TO_IDX(block_size, offset) ((offset) / block_size)

int camkes_virtqueue_buffer_alloc(virtqueue_driver_t *virtqueue, void **buf, size_t alloc_size)
{
    if (!virtqueue) {
        return -1;
    }

    struct vq_buf_alloc *allocator = virtqueue->cookie;

    if (alloc_size > allocator->block_size) {
        ZF_LOGE("Error: invalid alloc size");
        return -1;
    }
    if (allocator->head == allocator->free_list_size) {
        ZF_LOGE("Error: ran out of memory");
        return -1;
    }
    *buf = allocator->buffer + IDX_TO_OFFSET(allocator->block_size, allocator->head);
    allocator->head = allocator->free_list[allocator->head];
    return 0;
}

void camkes_virtqueue_buffer_free(virtqueue_driver_t *virtqueue, void *buffer)
{
    if (!virtqueue) {
        ZF_LOGE("virtqueue is NULL");
        return;
    }

    struct vq_buf_alloc *allocator = virtqueue->cookie;
    int idx = OFFSET_TO_IDX(allocator->block_size, (uintptr_t)buffer - (uintptr_t)(allocator->buffer));

    if (idx < 0 || idx >= allocator->free_list_size) {
        ZF_LOGE("Warning: invalid buffer");
        return;
    }
    allocator->free_list[idx] = allocator->head;
    allocator->head = idx;
}

static camkes_virtqueue_channel_t *get_virtqueue_channel(virtqueue_role_t role, unsigned int camkes_virtqueue_id)
{
    /* Check that the virtqueue id is in a valid range */
    if (camkes_virtqueue_id > MAX_CAMKES_VIRTQUEUE_ID) {
        return NULL;
    }
    /* Return error if the given virtqueue channel hasn't been initialized */
    if (camkes_virtqueue_channels[camkes_virtqueue_id].role == VIRTQUEUE_UNASSIGNED) {
        return NULL;
    }
    camkes_virtqueue_channel_t *channel = &camkes_virtqueue_channels[camkes_virtqueue_id];
    /* Check that the buffer is not NULL */
    if (channel->channel_buffer == NULL) {
        return NULL;
    }

    if (channel->role != role) {
        ZF_LOGE("role provided does not match role trying to bind to.");
        return NULL;
    }

    return channel;
}


int camkes_virtqueue_get_id_from_name(const char *interface_name)
{
    for (int i = 0; i < MAX_CAMKES_VIRTQUEUE_ID; i++) {
        if (strncmp(interface_name, camkes_virtqueue_channels[i].interface_name, 200) == 0) {
            return i;
        }
    }
    return -1;
}

int camkes_virtqueue_driver_init_with_recv(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id,
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge)
{
    if (driver == NULL) {
        return -1;
    }

    camkes_virtqueue_channel_t *channel = get_virtqueue_channel(VIRTQUEUE_DRIVER, camkes_virtqueue_id);
    if (channel == NULL) {
        ZF_LOGE("Failed to get channel");
        return -1;
    }

    if (recv_notification != NULL) {
        *recv_notification = channel->recv_notification;
    }
    if (recv_badge != NULL) {
        *recv_badge = channel->recv_badge;
    }

    return camkes_virtqueue_driver_init_common(driver, channel->channel_buffer, channel->queue_len, channel->channel_buffer_size,
                                               channel->notify, BLOCK_SIZE) ? -1 : 0;
}

int camkes_virtqueue_device_init_with_recv(virtqueue_device_t *device, unsigned int camkes_virtqueue_id,
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge)
{
    if (device == NULL) {
        return -1;
    }

    camkes_virtqueue_channel_t *channel = get_virtqueue_channel(VIRTQUEUE_DEVICE, camkes_virtqueue_id);
    if (channel == NULL) {
        ZF_LOGE("Failed to get channel");
        return -1;
    }

    if (recv_notification != NULL) {
        *recv_notification = channel->recv_notification;
    }
    if (recv_badge != NULL) {
        *recv_badge = channel->recv_badge;
    }

    return camkes_virtqueue_device_init_common(device, channel->channel_buffer, channel->queue_len, channel->notify) ? -1 : 0;
}

void *camkes_virtqueue_device_offset_to_buffer(virtqueue_device_t *virtqueue, uintptr_t offset)
{
    return virtqueue->cookie + offset;
}

void *camkes_virtqueue_driver_offset_to_buffer(virtqueue_driver_t *virtqueue, uintptr_t offset)
{
    struct vq_buf_alloc *allocator = virtqueue->cookie;

    return allocator->buffer + offset;
}

int camkes_virtqueue_driver_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size)
{
    uintptr_t base_offset = (uintptr_t)(((struct vq_buf_alloc *)vq->cookie)->buffer);
    uintptr_t buf_offset = (uintptr_t)buffer - base_offset;
    virtqueue_ring_object_t handle;

    virtqueue_init_ring_object(&handle);
    if (!virtqueue_add_available_buf(vq, &handle, (void *)buf_offset, size, VQ_RW)) {
        ZF_LOGE("Error while enqueuing available buffer");
        return -1;
    }
    return 0;
}

static int chain_vq_buf(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                        void *buffer, size_t size)
{
    struct vq_buf_alloc *allocator = vq->cookie;
    uintptr_t offset = (uintptr_t)buffer - (uintptr_t)(allocator->buffer);

    if (!virtqueue_add_available_buf(vq, handle, (void *)offset, size, VQ_RW)) {
        ZF_LOGE("Error while chaining available buffer");
        return -1;
    }
    return 0;
}

int camkes_virtqueue_driver_scatter_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size)
{
    size_t sent = 0;
    virtqueue_ring_object_t handle;
    virtqueue_init_ring_object(&handle);

    while (sent < size) {
        void *vq_buf = NULL;
        size_t to_send = 0;

        to_send = size - sent < BLOCK_SIZE ? size - sent : BLOCK_SIZE;
        if (camkes_virtqueue_buffer_alloc(vq, &vq_buf, to_send)) {
            ZF_LOGE("Error: could not allocate virtqueue buffer");
            return -1;
        }
        if (buffer) {
            memcpy(vq_buf, buffer + sent, to_send);
        }
        if (chain_vq_buf(vq, &handle, vq_buf, to_send)) {
            return -1;
        }
        sent += to_send;
    }
    return 0;
}

int camkes_virtqueue_driver_gather_copy_buffer(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                                               void *buffer, size_t size)
{
    size_t copied = 0;
    void *used_buf;
    unsigned buf_size;
    vq_flags_t flag;

    while (camkes_virtqueue_driver_gather_buffer(vq, handle, &used_buf, &buf_size, &flag) == 0) {
        size_t to_copy = copied + buf_size > size ? size - copied : buf_size;

        if (to_copy) {
            memcpy(buffer + copied, used_buf, to_copy);
        }
        copied += to_copy;
        camkes_virtqueue_buffer_free(vq, used_buf);
    }
    return 0;
}

int camkes_virtqueue_device_scatter_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                                void *buffer, size_t size)
{
    size_t sent = 0;

    while (sent < size) {
        void *avail_buf;
        unsigned buf_size;
        size_t to_copy;
        vq_flags_t flag;

        if (camkes_virtqueue_device_gather_buffer(vq, handle, &avail_buf, &buf_size, &flag)) {
            virtqueue_add_used_buf(vq, handle, sent);
            return -1;
        }
        to_copy = size - sent < buf_size ? size - sent : buf_size;
        memcpy(avail_buf, buffer + sent, to_copy);
        sent += to_copy;
    }
    virtqueue_add_used_buf(vq, handle, sent);
    return 0;
}

int camkes_virtqueue_device_gather_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                               void *buffer, size_t size)
{
    size_t sent = 0;

    while (sent < size) {
        void *avail_buf;
        unsigned buf_size;
        size_t to_copy;
        vq_flags_t flag;

        if (camkes_virtqueue_device_gather_buffer(vq, handle, &avail_buf, &buf_size, &flag)) {
            virtqueue_add_used_buf(vq, handle, sent);
            return -1;
        }
        to_copy = size - sent < buf_size ? size - sent : buf_size;
        memcpy(buffer + sent, avail_buf, to_copy);
        sent += to_copy;
    }
    virtqueue_add_used_buf(vq, handle, sent);
    return 0;
}

int camkes_virtqueue_driver_gather_buffer(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag)
{
    uintptr_t buf_offset;
    if (!virtqueue_gather_used(vq, handle, (void **)&buf_offset, size, flag)) {
        return -1;
    }
    *buffer = camkes_virtqueue_driver_offset_to_buffer(vq, (uintptr_t) buf_offset);
    return 0;
}

int camkes_virtqueue_device_gather_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag)
{
    uintptr_t buf_offset;
    if (!virtqueue_gather_available(vq, handle, (void **)&buf_offset, size, flag)) {
        return -1;
    }
    *buffer = camkes_virtqueue_device_offset_to_buffer(vq, (uintptr_t) buf_offset);
    return 0;
}

int camkes_virtqueue_channel_num(void)
{
    /* Return number of registered virtqueue channels */
    return num_registered_virtqueue_channels;
}
