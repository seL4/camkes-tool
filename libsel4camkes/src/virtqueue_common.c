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

int camkes_virtqueue_driver_init_common(virtqueue_driver_t *driver, void *buffer, size_t buffer_size,
                                        void (*notify)(void), size_t block_size)
{
    /* Don't check for notify, as it can be NULL in some situations */
    if (!driver || !buffer) {
        return EINVAL;
    }

    void *avail_ring = buffer;
    void *used_ring = avail_ring + sizeof(vq_vring_avail_t);
    void *desc = used_ring + sizeof(vq_vring_used_t);

    void *usable_buffer_start = desc + sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE;
    unsigned usable_len = buffer_size - (sizeof(vq_vring_avail_t) + sizeof(vq_vring_used_t) +
                                         sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE);
    struct vq_buf_alloc *allocator = init_vq_allocator(usable_buffer_start, usable_len, block_size);
    if (!allocator) {
        return ENOMEM;
    }

    virtqueue_init_driver(driver, avail_ring, used_ring, desc, notify, allocator);

    virtqueue_init_desc_table(desc);
    virtqueue_init_avail_ring(desc);
    virtqueue_init_used_ring(desc);

    return 0;
}

int camkes_virtqueue_device_init_common(virtqueue_device_t *device, void *buffer, void (*notify)(void))
{
    /* Don't check for notify, as it can be NULL in some situations */
    if (!device || !buffer) {
        return EINVAL;
    }

    void *avail_ring = buffer;
    void *used_ring = avail_ring + sizeof(vq_vring_avail_t);
    void *desc = used_ring + sizeof(vq_vring_used_t);
    void *cookie = desc + sizeof(vq_vring_desc_t) * DESC_TABLE_SIZE;
    virtqueue_init_device(device, avail_ring, used_ring, desc, notify, cookie);

    return 0;
}
