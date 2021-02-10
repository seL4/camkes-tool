/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/sel4.h>
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

typedef enum virtqueue_role {
    VIRTQUEUE_UNASSIGNED,
    VIRTQUEUE_DRIVER,
    VIRTQUEUE_DEVICE
} virtqueue_role_t;

typedef struct virtqueue_channel {
    volatile void *channel_buffer;
    size_t channel_buffer_size;
    unsigned queue_len;
    void (*notify)(void);
    seL4_CPtr recv_notification;
    seL4_Word recv_badge;
    virtqueue_role_t role;
    uint8_t buffer_allocated;
    const char *interface_name;
} camkes_virtqueue_channel_t;

/*
 * Global array that contains all the registered virtqueue channels for a
 * component. Virtqueue channels are stored in the array based on their
 * configured id
 */
extern camkes_virtqueue_channel_t camkes_virtqueue_channels[MAX_CAMKES_VIRTQUEUE_ID + 1];

/* The number of virtqueue channels registered to a component */
extern int num_registered_virtqueue_channels;

/**
 * @brief      Convert a string name to a camkes virtqueue channel id.
 *
 * When a camkes virtqueue is registered, a numeric ID and a string name are provided
 * to identify it with. This function translates from the string name to numerical ID.
 *
 * @param[in]  interface_name  The interface name
 *
 * @return     Returns a valid ID or -1 on error.
 */
int camkes_virtqueue_get_id_from_name(const char *interface_name);

/* Initialise a virtqueue_driver_t object from a registered virtqueue channel
 * @param virtqueue_driver_t Pointer to set with the allocated virtqueue_driver_t object
 * @param camkes_virtqueue_id The unique id of the registered virtqueue channel. This
 * indexes into the 'camkes_virtqueue_channels' array
 * @param recv_notification Capability to notification object for receiving events on.
 * @param recv_badge Badge value that received notifications will have.
 *        If recv_notification or recv_badge are NULL then they won't be returned.
 * @return Positive 0 on success, -1 on error
 */
int camkes_virtqueue_driver_init_with_recv(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id,
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge);

static inline int camkes_virtqueue_driver_init(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id)
{
    return camkes_virtqueue_driver_init_with_recv(driver, camkes_virtqueue_id, NULL, NULL);
}

/* Initialise a virtqueue_device_t object from a registered virtqueue channel
 * @param virtqueue_device_t Pointer to set with the allocated virtqueue_device_t object
 * @param camkes_virtqueue_id The unique id of the registered virtqueue channel. This
 * indexes into the 'camkes_virtqueue_channels' array
 * @param recv_notification Capability to notification object for receiving events on.
 * @param recv_badge Badge value that received notifications will have.
 *        If recv_notification or recv_badge are NULL then they won't be returned.
 * @return Positive 0 on success, -1 on error
 */
int camkes_virtqueue_device_init_with_recv(virtqueue_device_t *device, unsigned int camkes_virtqueue_id,
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge);

static inline int camkes_virtqueue_device_init(virtqueue_device_t *device, unsigned int camkes_virtqueue_id)
{
    return camkes_virtqueue_device_init_with_recv(device, camkes_virtqueue_id, NULL, NULL);
}

/* Allocates a virtqueue buffer that the given 'virtqueue_driver_t' can use to communicate with
 * @param virtqueue_driver_t Pointer to the virtqueue_driver_t object we are allocating a buffer for
 * @param buffer A pointer to set with the allocated region of memory
 * @param alloc_size Size of memory to allocate
 * @return Positive 0 on success, -1 on error
 */
int camkes_virtqueue_buffer_alloc(virtqueue_driver_t *virtqueue, void **buf, size_t alloc_size);

/* Frees a virtqueue buffer that the given 'virtqueue_driver_t' is using
 * @param virtqueue_driver_t Pointer to the virtqueue object we are free a buffer for
 * @param buffer A pointer to the allocated region of memory we wish to free
 */
void camkes_virtqueue_buffer_free(virtqueue_driver_t *virtqueue, void *buffer);

/* Convert an offset in shared memory to a pointer in the device vspace
 * @param virtqueue the device side virtqueue
 * @param offset the offset to convert
 * @return the converted pointer
 */
void *camkes_virtqueue_device_offset_to_buffer(virtqueue_device_t *virtqueue, uintptr_t offset);

/* Convert an offset in shared memory to a pointer in the driver vspace
 * @param virtqueue the driver side virtqueue
 * @param offset the offset to convert
 * @return the converted pointer
 */
void *camkes_virtqueue_driver_offset_to_buffer(virtqueue_driver_t *virtqueue, uintptr_t offset);

/* Send exactly one buffer to the virtqueue (add it to the available ring). Performs the pointer
 * to offset conversion. Doesn't notify the other side. Doesn't scatter the buffer, so the scatterlist
 * will only contain one buffer.
 * @param vq the driver side virtqueue
 * @param buffer a pointer (in driver vspace) to the buffer to send
 * @param size the size of the buffer
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_driver_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size);

/* Scatter and send one buffer (add to the available ring). Performs the pointer to offset conversion.
 * Doesn't notify the other side. Scatters the buffer into chunks of BLOCK_SIZE, so the buffer can have
 * an arbitrary size, and the scatterlist will contain several buffers.
 * @param vq the driver side virtqueue
 * @param buffer the buffer to add
 * @param size the size of the buffer
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_driver_scatter_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size);

/* Takes a handle (obtained from a get_used_buffer invocation), iterates through all the buffers in
 * the scatterlist and copies them into the buffer given as parameter. Once each buffer has been copied,
 * it gets freed.
 * @param vq the driver side virtqueue
 * @param handle the iterator on the used ring object
 * @param buffer a pointer to the buffer to copy into
 * @param size the size of the buffer we're passing
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_driver_gather_copy_buffer(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                                               void *buffer, size_t size);

/* Takes a handle (obtained from a get_available_buffer), iterates through all the buffers in the scatterlist
 * and scatter-copies the content of the buffer passed as parameter into them. Then move the ring object into
 * the used buffer ring.
 * @param vq the device side virtqueue
 * @param handle the iterator on the available ring object
 * @param buffer a pointer to the buffer to copy from
 * @param size the size of the buffer we're passing
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_device_scatter_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                                void *buffer, size_t size);

/* Takes a handle (obtained from a get_used_buffer invocation), iterates through all the buffers in
 * the scatterlist and copies them into the buffer given as parameter. Then adds the object onto the
 * used list.
 * @param vq the device side virtqueue
 * @param handle the iterator on the available ring object
 * @param buffer a pointer to the buffer to copy from
 * @param size the size of the buffer we're passing
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_device_gather_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                               void *buffer, size_t size);

/* Performs one iteration on the scatterlist pointed by the given handle: returns the next buffer in the list.
 * @param vq the driver side virtqueue
 * @param handle the iterator on the used ring object
 * @param buffer a pointer to the address of the buffer to be returned
 * @param size a pointer to the size of the buffer to be returned
 * @param flag a pointer to the flag of the buffer getting returned
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_driver_gather_buffer(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag);

/* Performs one iteration on the scatterlist pointed by the given handle: returns the next buffer in the list.
 * @param vq the device side virtqueue
 * @param handle the iterator on the available ring object
 * @param buffer a pointer to the address of the buffer to be returned
 * @param size a pointer to the size of the buffer to be returned
 * @param flag a pointer to the flag of the buffer getting returned
 * @return 0 on success, -1 on fail
 */
int camkes_virtqueue_device_gather_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag);

/* Returns the number of registered virtqueue channels
 * @return Number of registered virtqueue channels
 */
int camkes_virtqueue_channel_num(void);
