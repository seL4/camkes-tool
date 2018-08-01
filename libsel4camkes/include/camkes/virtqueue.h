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

/*
 * Represents a shared window between two components
 * that can be used as a basis for a virtqueue. This
 * primary purpose of this structure is to encapsulate
 * the shared memory buffer and role of the component
 * (DEVICE or DRIVER) when using this channel
 * for virtqueue-based communication.
 *
 * It is expected that a CAmkES connection template will
 * register a single virtqueue channel.
 */
typedef struct virtqueue_channel {
    volatile void *channel_buffer;
    size_t channel_buffer_size;
    notify_fn_t notify;
    virtqueue_role_t role;
    uint8_t buffer_allocated;
} virtqueue_channel_t;

/*
 * Global array that contains all the registered virtqueue channels for a
 * component. Virtqueue channels are stored in the array based on their
 * configured id
 */
extern virtqueue_channel_t virtqueue_channels[MAX_CAMKES_VIRTQUEUE_ID + 1];

/* The number of virtqueue channels registered to a component */
extern int num_registered_virtqueue_channels;

/* Initialise a virtqueue object from a registered virtqueue channel
 * @param virtqueue Pointer to set with the allocated virtqueue object
 * @param camkes_virtqueue_id The unique id of the registered virtqueue channel. This
 * indexes into the 'virtqueue_channels' array
 * @return Positive 0 on success, -1 on error
 */
int init_camkes_virtqueue(virtqueue_t **virtqueue, unsigned int camkes_virtqueue_id);

/* Allocates a virtqueue buffer that the given 'virtqueue' can use to communicate with
 * @param virtqueue Pointer to the virtqueue object we are allocating a buffer for
 * @param buffer A pointer to set with the allocated region of memory
 * @param alloc_size Size of memory to allocate
 * @return Positive 0 on success, -1 on error
 */
int alloc_camkes_virtqueue_buffer(virtqueue_t *virtqueue, volatile void **buffer, size_t alloc_size);

/* Frees a virtqueue buffer that the given 'virtqueue' is using
 * @param virtqueue Pointer to the virtqueue object we are free a buffer for
 * @param buffer A pointer to the allocated region of memory we wish to free
 */
void free_camkes_virtqueue_buffer(virtqueue_t *virtqueue, void *buffer);

/* Returns the number of registered virtqueue channels
 * @return Number of registered virtqueue channels
 */
int query_num_virtqueue_channels(void);
