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

#pragma once

#include <virtqueue.h>
#include <stddef.h>
#include <inttypes.h>

/* Max camkes virtqueue id */
#define MAX_CAMKES_VIRTQUEUE_ID 100

typedef struct virtqueue_channel {
    volatile void *channel_buffer;
    size_t channel_buffer_size;
    notify_fn_t notify;
    virtqueue_role_t role;
    uint8_t buffer_allocated;
} virtqueue_channel_t;

extern virtqueue_channel_t virtqueue_channels[MAX_CAMKES_VIRTQUEUE_ID + 1];
extern int num_registered_virtqueue_channels;

int init_camkes_virtqueue(virtqueue_t **virtqueue, unsigned int camkes_virtqueue_id);
int alloc_camkes_virtqueue_buffer(virtqueue_t *virtqueue, volatile void **buffer, size_t alloc_size);
void free_camkes_virtqueue_buffer(virtqueue_t *virtqueue, void *buffer);

int query_num_virtqueue_channels(void);
