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

#include <virtqueue.h>

#include <camkes/io.h>
#include <camkes/virtqueue.h>

struct vq_buf_alloc {
    void *buffer;
    unsigned len;
    unsigned block_size;
    unsigned free_list_size;
    unsigned *free_list;
    unsigned head;
};

struct vq_buf_alloc *init_vq_allocator(void *mem_pool, unsigned len, size_t block_size);

int camkes_virtqueue_driver_init_common(virtqueue_driver_t *driver, volatile void *buffer, size_t buffer_size,
                                        void (*notify)(void), size_t block_size);

int camkes_virtqueue_device_init_common(virtqueue_device_t *device, volatile void *buffer, void (*notify)(void));
