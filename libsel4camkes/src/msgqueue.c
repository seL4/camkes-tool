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
#include <camkes/msgqueue.h>
#include <camkes/msgqueue_template.h>
#include <camkes/virtqueue.h>
#include <sel4/sel4.h>
#include <utils/util.h>

#include "virtqueue_common.h"

int camkes_msgqueue_sender_init(int msgqueue_id, camkes_msgqueue_sender_t *sender)
{
    if (!sender) {
        ZF_LOGE("sender is NULL");
        return EINVAL;
    }

    if (sender->initialised) {
        return 0;
    }

    camkes_msgqueue_channel_t *msgqueue_channel = camkes_msgqueue_channel_get(msgqueue_id, MSGQUEUE_SENDER);
    if (!msgqueue_channel) {
        ZF_LOGE("Failed to retrieve an initialised sender channel with ID %d", msgqueue_id);
        return EINVAL;
    }

    size_t aligned_message_size = msgqueue_channel->message_size;
    if (!IS_POWER_OF_2(msgqueue_channel->message_size)) {
        aligned_message_size = NEXT_POWER_OF_2(msgqueue_channel->message_size);
    }

    int error = camkes_virtqueue_driver_init_common(&sender->sender_channel, msgqueue_channel->buffer,
                                                    msgqueue_channel->queue_len,
                                                    msgqueue_channel->buffer_size, msgqueue_channel->sender_funcs.notify,
                                                    aligned_message_size);
    if (error) {
        return error;
    }

    sender->message_size = msgqueue_channel->message_size;
    sender->initialised = true;

    return 0;
}

int camkes_msgqueue_receiver_init(int msgqueue_id, camkes_msgqueue_receiver_t *receiver)
{
    if (!receiver) {
        ZF_LOGE("receiver is NULL");
        return EINVAL;
    }

    if (receiver->initialised) {
        return 0;
    }

    camkes_msgqueue_channel_t *msgqueue_channel = camkes_msgqueue_channel_get(msgqueue_id, MSGQUEUE_RECEIVER);
    if (!msgqueue_channel) {
        ZF_LOGE("Failed to retrieve an initialised receiver channel with ID %d", msgqueue_id);
        return EINVAL;
    }

    int error = camkes_virtqueue_device_init_common(&receiver->receiver_channel,
                                                    msgqueue_channel->buffer, msgqueue_channel->queue_len, NULL);
    if (error) {
        return error;
    }

    receiver->message_size = msgqueue_channel->message_size;
    receiver->poll = msgqueue_channel->receiver_funcs.poll;
    receiver->wait = msgqueue_channel->receiver_funcs.wait;
    receiver->initialised = true;

    return 0;
}

static void *msgqueue_alloc_buffer(camkes_msgqueue_sender_t *sender)
{
    void *ret_buffer = NULL;
    virtqueue_ring_object_t handle = {0};
    unsigned len = 0;
    UNUSED unsigned size = 0;
    UNUSED vq_flags_t flag = {0};
    int error = 0;

    /* Grab a used buffer if possible */
    if (virtqueue_get_used_buf(&sender->sender_channel, &handle, &len)) {
        error = camkes_virtqueue_driver_gather_buffer(&sender->sender_channel, &handle,
                                                      (void **) &ret_buffer, &size, &flag);
        ZF_LOGF_IF(error, "Failed to get a 'used' buffer even though there exists one");
        return ret_buffer;
    }

    /* Allocate a fresh buffer */
    error = camkes_virtqueue_buffer_alloc(&sender->sender_channel, &ret_buffer, sender->message_size);
    if (error) {
        return NULL;
    }

    return ret_buffer;
}

int camkes_msgqueue_send(camkes_msgqueue_sender_t *sender, void *message, size_t message_size)
{
    if (!sender || !message) {
        return EINVAL;
    }

    if (!sender->initialised) {
        return EINVAL;
    }

    if (message_size > sender->message_size) {
        ZF_LOGE("Message size is too large for this msgqueue");
        return EMSGSIZE;
    }

    /* Grab a buffer from the channel */
    void *msgqueue_buf = msgqueue_alloc_buffer(sender);
    if (!msgqueue_buf) {
        return ENOMEM;
    }

    /* Copy the contents of the received buffer */
    memcpy((void *) msgqueue_buf, message, message_size);

    /* Now enqueue it on the virtqueue */
    int error = camkes_virtqueue_driver_send_buffer(&sender->sender_channel, msgqueue_buf, message_size);
    if (error) {
        memset((void *) msgqueue_buf, 0, message_size);
        camkes_virtqueue_buffer_free(&sender->sender_channel, msgqueue_buf);
        return ECOMM;
    }

    sender->sender_channel.notify();

    return 0;
}

int camkes_msgqueue_poll(camkes_msgqueue_receiver_t *receiver)
{
    if (!receiver) {
        return EINVAL;
    }

    if (!receiver->initialised) {
        return EINVAL;
    }

    return receiver->poll();
}

int camkes_msgqueue_wait(camkes_msgqueue_receiver_t *receiver)
{
    if (!receiver) {
        return EINVAL;
    }

    if (!receiver->initialised) {
        return EINVAL;
    }

    receiver->wait();

    return 0;
}

int camkes_msgqueue_get(camkes_msgqueue_receiver_t *receiver, void *buffer, size_t buffer_size)
{
    if (!receiver || !buffer) {
        return EINVAL;
    }

    if (!receiver->initialised) {
        return EINVAL;
    }

    if (buffer_size < receiver->message_size) {
        ZF_LOGE("Buffer is too small for the message");
        return EMSGSIZE;
    }

    /* Try to get a message from the queue */
    virtqueue_ring_object_t handle = {0};

    if (!virtqueue_get_available_buf(&receiver->receiver_channel, &handle)) {
        return ENOMSG;
    }

    void *message = NULL;
    unsigned message_len = 0;
    UNUSED vq_flags_t flags = {0};

    int error = camkes_virtqueue_device_gather_buffer(&receiver->receiver_channel, &handle, &message, &message_len, &flags);
    ZF_LOGF_IF(error, "Failed to dequeue a message from the queue even though there is one");

    /* Copy it over and then add the buffer to the used ring */
    assert(buffer_size >= message_len);
    memcpy(buffer, message, message_len);

    virtqueue_add_used_buf(&receiver->receiver_channel, &handle, message_len);

    return 0;
}
