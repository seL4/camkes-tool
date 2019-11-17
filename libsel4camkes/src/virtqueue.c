/*
 * Copyright 2019, Data61
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
#include <string.h>
#include <camkes/virtqueue.h>
#include <utils/util.h>
#include <platsupport/io.h>

#define BLOCK_SIZE 128
#define IDX_TO_OFFSET(idx) (BLOCK_SIZE*(idx))
#define OFFSET_TO_IDX(offset) ((offset)/BLOCK_SIZE)

struct vq_buf_alloc {
    volatile void *buffer;
    unsigned len;
    unsigned free_list_size;
    unsigned *free_list;
    unsigned head;
};

int camkes_virtqueue_buffer_alloc(virtqueue_driver_t *virtqueue, void **buf, size_t alloc_size)
{
    struct vq_buf_alloc *allocator;

    if (alloc_size > BLOCK_SIZE) {
        ZF_LOGE("Error: invalid alloc size");
        return -1;
    }
    allocator = virtqueue->cookie;
    if (allocator->head == allocator->free_list_size) {
        ZF_LOGE("Error: ran out of memory");
        return -1;
    }
    *buf = allocator->buffer + IDX_TO_OFFSET(allocator->head);
    allocator->head = allocator->free_list[allocator->head];
    return 0;
}

void camkes_virtqueue_buffer_free(virtqueue_driver_t *virtqueue, void *buffer)
{
    struct vq_buf_alloc *allocator = virtqueue->cookie;
    int idx = OFFSET_TO_IDX((uintptr_t)buffer - (uintptr_t)(allocator->buffer));

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


int camkes_virtqueue_driver_init(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id)
{
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

    volatile void *avail_ring = channel->channel_buffer;
    volatile void *used_ring = avail_ring + sizeof(vq_vring_avail_t);
    volatile void *desc = used_ring + sizeof(vq_vring_used_t);
    struct vq_buf_alloc *cookie; /* TODO */
    if (ps_calloc(&malloc_ops, 1, sizeof(struct vq_buf_alloc), (void **)&cookie)) {
        ZF_LOGE("Failed to allocate alloc structure");
        return -1;
    }
    cookie->buffer = desc + sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE;
    cookie->len = channel->channel_buffer_size -
                  (sizeof(vq_vring_avail_t) + sizeof(vq_vring_used_t) + sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE);
    cookie->free_list_size = cookie->len / BLOCK_SIZE;
    if (ps_calloc(&malloc_ops, 1, cookie->free_list_size * sizeof(*cookie->free_list), (void **)(&cookie->free_list))) {
        ZF_LOGE("Failed to allocate free_list");
        ps_free(&malloc_ops, sizeof(struct vq_buf_alloc), cookie);
        return -1;
    }
    unsigned i;
    for (i = 0; i < cookie->free_list_size; i++) {
        cookie->free_list[i] = i + 1;
    }
    cookie->head = 0;
    virtqueue_init_driver(driver, avail_ring, used_ring, desc, channel->notify, cookie);

    virtqueue_init_desc_table(desc);
    virtqueue_init_avail_ring(avail_ring);
    virtqueue_init_used_ring(used_ring);

    return 0;

}

int camkes_virtqueue_device_init(virtqueue_device_t *device, unsigned int camkes_virtqueue_id)
{
    if (device == NULL) {
        return -1;
    }

    camkes_virtqueue_channel_t *channel = get_virtqueue_channel(VIRTQUEUE_DEVICE, camkes_virtqueue_id);
    if (channel == NULL) {
        ZF_LOGE("Failed to get channel");
        return -1;
    }

    volatile void *avail_ring = channel->channel_buffer;
    volatile void *used_ring = avail_ring + sizeof(vq_vring_avail_t);
    volatile void *desc = used_ring + sizeof(vq_vring_used_t);
    void *cookie = desc + sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE;
    virtqueue_init_device(device, avail_ring, used_ring, desc, channel->notify, cookie);

    return 0;
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

int camkes_virtqueue_driver_send_buffer(virtqueue_driver_t *vq, volatile void *buffer, size_t size)
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
