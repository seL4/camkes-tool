/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <virtqueue.h>

#include <camkes/io.h>

#include "virtqueue_common.h"

struct vq_buf_alloc *init_vq_allocator(void *mem_pool, unsigned len, size_t block_size)
{
    ps_malloc_ops_t malloc_ops;
    int error = camkes_ps_malloc_ops(&malloc_ops);
    if (error) {
        return NULL;
    }

    struct vq_buf_alloc *allocator = NULL;

    error = ps_calloc(&malloc_ops, 1, sizeof(*allocator), (void **)&allocator);
    if (error) {
        return NULL;
    }

    allocator->buffer = mem_pool;
    allocator->len = len;
    allocator->free_list_size = len / block_size;
    allocator->block_size = block_size;
    if (ps_calloc(&malloc_ops, 1, allocator->free_list_size * sizeof(*(allocator->free_list)),
                  (void **)(&allocator->free_list))) {
        ZF_LOGE("Failed to allocate free_list");
        ps_free(&malloc_ops, sizeof(*allocator), allocator);
        return NULL;
    }
    unsigned i;
    for (i = 0; i < allocator->free_list_size; i++) {
        allocator->free_list[i] = i + 1;
    }
    allocator->head = 0;

    return allocator;
}

int camkes_virtqueue_driver_init_common(virtqueue_driver_t *driver, volatile void *buffer, unsigned queue_len,
                                        size_t buffer_size, void (*notify)(void), size_t block_size)
{
    /* Don't check for notify, as it can be NULL in some situations */
    if (!driver || !buffer) {
        return EINVAL;
    }

    void *avail_ring = (void *) buffer;
    void *used_ring = avail_ring + sizeof(vq_vring_avail_t) + sizeof(uint16_t) * queue_len;
    void *desc = used_ring + sizeof(vq_vring_used_t) + sizeof(struct vq_vring_used_elem) * queue_len;

    void *usable_buffer_start = desc + sizeof(vq_vring_desc_t) * queue_len;
    unsigned usable_len = buffer_size - (sizeof(vq_vring_avail_t) + sizeof(vq_vring_used_t) +
                                         sizeof(uint16_t) * queue_len + sizeof(struct vq_vring_used_elem) * queue_len +
                                         sizeof(vq_vring_desc_t) * queue_len);
    struct vq_buf_alloc *allocator = init_vq_allocator(usable_buffer_start, usable_len, block_size);
    if (!allocator) {
        return ENOMEM;
    }

    virtqueue_init_driver(driver, queue_len, avail_ring, used_ring, desc, notify, allocator);


    return 0;
}

int camkes_virtqueue_device_init_common(virtqueue_device_t *device, volatile void *buffer, unsigned queue_len,
                                        void (*notify)(void))
{
    /* Don't check for notify, as it can be NULL in some situations */
    if (!device || !buffer) {
        return EINVAL;
    }

    void *avail_ring = (void *) buffer;
    void *used_ring = avail_ring + sizeof(vq_vring_avail_t) + sizeof(uint16_t) * queue_len;
    void *desc = used_ring + sizeof(vq_vring_used_t) + sizeof(struct vq_vring_used_elem) * queue_len;
    void *cookie = desc + sizeof(vq_vring_desc_t) * queue_len;
    virtqueue_init_device(device, queue_len, avail_ring, used_ring, desc, notify, cookie);

    return 0;
}
