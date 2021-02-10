/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <virtqueue.h>
#include <camkes/virtqueue.h>
#include <utils/util.h>

/* This file contains FFI functions for interacting with virtqueues from CakeML.
 *
 * Some functions are simple wrappers around their C counterparts, whilst others
 * like `driver_send` provide slightly more "functional" abstractions over the low-level
 * interface, with the aim of insulating CakeML from some of the buffer mangling that is
 * more easily accomplished in C. In the future we may want to tear these abstractions down
 * or indeed implement the basic functionality of the virtqueues library in CakeML itself.
 *
 * By convention, the first byte of the array returned will be FFI_SUCCESS (0) if the call
 * succeeded, or FFI_FAILURE (1) if it did not. We may want to add more descriptive errors
 * in the future.
 */

#define FFI_SUCCESS 0
#define FFI_FAILURE 1

void ffivirtqueue_device_init(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_device_t *virtqueue;
    virtqueue = (virtqueue_device_t *)malloc(sizeof(virtqueue_device_t));
    if (!virtqueue) {
        ZF_LOGE("%s: unable to alloc a new virtqueue device", __func__);
        a[0] = FFI_FAILURE;
        return;
    }

    int32_t virtqueue_id;
    memcpy(&virtqueue_id, a + 1, sizeof(virtqueue_id));

    int err = camkes_virtqueue_device_init(virtqueue, virtqueue_id);

    if (err) {
        ZF_LOGE("%s: unable to create a new virtqueue device", __func__);
        a[0] = FFI_FAILURE;
    } else {
        memcpy(a + 1, &virtqueue, sizeof(virtqueue_device_t *));
        a[0] = FFI_SUCCESS;
    }
}

void ffivirtqueue_driver_init(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_driver_t *virtqueue;
    virtqueue = (virtqueue_driver_t *)malloc(sizeof(virtqueue_driver_t));
    if (!virtqueue) {
        ZF_LOGE("%s: unable to alloc a new virtqueue driver", __func__);
        a[0] = FFI_FAILURE;
        return;
    }
    int32_t virtqueue_id;
    memcpy(&virtqueue_id, a + 1, sizeof(virtqueue_id));

    int err = camkes_virtqueue_driver_init(virtqueue, virtqueue_id);

    if (err) {
        ZF_LOGE("%s: unable to create a new virtqueue driver", __func__);
        a[0] = FFI_FAILURE;
    } else {
        memcpy(a + 1, &virtqueue, sizeof(virtqueue_driver_t *));
        a[0] = FFI_SUCCESS;
    }
}

void ffivirtqueue_device_poll(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_device_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));

    int poll_res = VQ_DEV_POLL(virtqueue);

    memcpy(a + 1, &poll_res, sizeof(poll_res));
    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_driver_poll(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_driver_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));

    int poll_res = VQ_DRV_POLL(virtqueue);

    memcpy(a + 1, &poll_res, sizeof(poll_res));
    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_device_recv(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_device_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));

    // 1. Dequeue available buffer from virtqueue
    void *available_buff = NULL;
    size_t buf_size = 0;
    vq_flags_t flag;
    virtqueue_ring_object_t handle;

    if (!virtqueue_get_available_buf(virtqueue, &handle)) {
        ZF_LOGE("%s: device dequeue failed", __func__);
        a[0] = FFI_FAILURE;
        return;
    }

    int dequeue_res = camkes_virtqueue_device_gather_buffer(virtqueue, &handle,
                                                            &available_buff, &buf_size, &flag);
    if (dequeue_res) {
        ZF_LOGE("%s: device buffer gather failed", __func__);
        a[0] = FFI_FAILURE;
        return;
    }

    // 2. Copy to CakeML buffer
    memcpy(a + 1, &buf_size, sizeof(buf_size));
    memcpy(a + 1 + sizeof(buf_size), available_buff, buf_size);

    // 3. Enqueue the buffer on the used queue to let the other end know we've finished with it
    if (!virtqueue_add_used_buf(virtqueue, &handle, 0)) {
        ZF_LOGE("Unable to add used buffer");
        a[0] = FFI_FAILURE;
        return;
    }
    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_device_signal(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_device_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));
    virtqueue->notify();
    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_driver_signal(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_driver_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));
    virtqueue->notify();
    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_driver_recv(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_driver_t *virtqueue;
    memcpy(&virtqueue, a + 1, sizeof(virtqueue));
    // 1. Dequeue used buffer from virtqueue
    void *used_buff = NULL;
    size_t buf_size = 0;
    uint32_t wr_len = 0;
    vq_flags_t flag;
    virtqueue_ring_object_t handle;
    if (!virtqueue_get_used_buf(virtqueue, &handle, &wr_len)) {
        ZF_LOGE("%s: driver dequeue failed", __func__);
        a[0] = FFI_FAILURE;
        return;
    }
    while (!camkes_virtqueue_driver_gather_buffer(virtqueue, &handle, &used_buff, &buf_size, &flag)) {
        /* Clean up and free the buffer we allocated */
        camkes_virtqueue_buffer_free(virtqueue, used_buff);
    }

    a[0] = FFI_SUCCESS;
}

void ffivirtqueue_driver_send(char *c, unsigned long clen, char *a, unsigned long alen)
{
    virtqueue_driver_t *virtqueue;
    int offset = 1;
    memcpy(&virtqueue, a + offset, sizeof(virtqueue));
    offset += sizeof(virtqueue);

    size_t message_len = 0;
    memcpy(&message_len, a + offset, sizeof(size_t));
    offset += sizeof(size_t);

    char *message = a + offset;

    void *alloc_buffer = NULL;
    int err = camkes_virtqueue_buffer_alloc(virtqueue, &alloc_buffer, message_len);
    if (err) {
        ZF_LOGE("%s: alloc for driver send failed", __func__);
        a[0] = FFI_FAILURE;
        return;
    }

    memcpy(alloc_buffer, (void *) message, message_len);

    if (camkes_virtqueue_driver_send_buffer(virtqueue, alloc_buffer, message_len) != 0) {
        camkes_virtqueue_buffer_free(virtqueue, alloc_buffer);
        a[0] = FFI_FAILURE;
        return;
    }

    a[0] = FFI_SUCCESS;
}
