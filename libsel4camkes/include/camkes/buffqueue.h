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

#include <buffqueue.h>
#include <stddef.h>
#include <inttypes.h>

/* Max camkes buffqueue id */
#define MAX_CAMKES_BUFFQUEUE_ID 100

typedef struct buffqueue_channel {
    volatile void *channel_buffer;
    size_t channel_buffer_size;
    notify_fn_t notify;
    buffqueue_role_t role;
    uint8_t buffer_allocated;
} buffqueue_channel_t;

buffqueue_channel_t buffqueue_channels[MAX_CAMKES_BUFFQUEUE_ID + 1];
int num_registered_buffqueue_channels;

int init_camkes_buffqueue(buffqueue_t **buffqueue, unsigned int camkes_buffqueue_id);
int alloc_camkes_buffqueue_buffer(buffqueue_t *buffqueue, void **buffer, size_t alloc_size);
void free_camkes_buffqueue_buffer(buffqueue_t *buffqueue, void *buffer);

int query_num_buffqueue_channels(void);
