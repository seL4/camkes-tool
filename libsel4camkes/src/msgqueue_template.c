/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <errno.h>
#include <camkes/msgqueue_template.h>
#include <utils/util.h>

camkes_msgqueue_channel_t camkes_msgqueue_channels[MAX_CAMKES_MSGQUEUE_ID];
int num_registered_msgqueue_channels;

static inline int msgqueue_channel_check_common(int msgqueue_id, void *buffer, size_t buffer_size,
                                                size_t message_size)
{
    if (msgqueue_id >= MAX_CAMKES_MSGQUEUE_ID) {
        ZF_LOGE("Supplied msgqueue_id is greater or equal to the maximum number of IDs");
        return -EINVAL;
    }

    if (num_registered_msgqueue_channels >= MAX_CAMKES_MSGQUEUE_ID) {
        ZF_LOGE("Trying to register more msgqueue channels than allowed");
        return -EINVAL;
    }

    if (camkes_msgqueue_channels[msgqueue_id].role != MSGQUEUE_UNASSIGNED) {
        ZF_LOGE("Trying to overwrite an initialised msgqueue channel");
        return -EINVAL;
    }

    if (!buffer) {
        ZF_LOGE("Trying to register a msgqueue channel with an empty buffer");
        return -EINVAL;
    }

    if (message_size >= buffer_size) {
        ZF_LOGE("The mesasage size of the channel is greater than the size of the buffer");
        return -EINVAL;
    }

    return 0;
}

static inline void msgqueue_channel_init_common(int msgqueue_id, void *buffer, unsigned queue_len,
                                                size_t buffer_size, size_t message_size)
{
    camkes_msgqueue_channels[msgqueue_id] = (camkes_msgqueue_channel_t) {
        0
    };
    camkes_msgqueue_channels[msgqueue_id].buffer = buffer;
    camkes_msgqueue_channels[msgqueue_id].queue_len = queue_len;
    camkes_msgqueue_channels[msgqueue_id].buffer_size = buffer_size;
    camkes_msgqueue_channels[msgqueue_id].message_size = message_size;
}

int camkes_msgqueue_channel_register_sender(int msgqueue_id, void *buffer, unsigned queue_len,
                                            size_t buffer_size, size_t message_size, void (*notify)(void))
{
    int res = msgqueue_channel_check_common(msgqueue_id, buffer, buffer_size, message_size);
    if (res) {
        return res;
    }

    if (!notify) {
        ZF_LOGE("Registering a sender msgqueue channel with empty 'notify' function pointer");
        return -EINVAL;
    }

    msgqueue_channel_init_common(msgqueue_id, buffer, queue_len, buffer_size, message_size);

    camkes_msgqueue_channels[msgqueue_id].role = MSGQUEUE_SENDER;
    camkes_msgqueue_channels[msgqueue_id].sender_funcs.notify = notify;

    return 0;
}

int camkes_msgqueue_channel_register_receiver(int msgqueue_id, void *buffer, unsigned queue_len,
                                              size_t buffer_size, size_t message_size, int (*poll)(void), void (*wait)(void))
{
    int res = msgqueue_channel_check_common(msgqueue_id, buffer, buffer_size, message_size);
    if (res) {
        return res;
    }

    if (!poll || !wait) {
        ZF_LOGE("Registering a receiver msgqueue channel with empty 'poll' and 'wait' function pointers");
        return -EINVAL;
    }

    msgqueue_channel_init_common(msgqueue_id, buffer, queue_len, buffer_size, message_size);

    camkes_msgqueue_channels[msgqueue_id].role = MSGQUEUE_RECEIVER;
    camkes_msgqueue_channels[msgqueue_id].receiver_funcs.poll = poll;
    camkes_msgqueue_channels[msgqueue_id].receiver_funcs.wait = wait;

    return 0;
}

camkes_msgqueue_channel_t *camkes_msgqueue_channel_get(int msgqueue_id, msgqueue_role_t role)
{
    if (msgqueue_id >= MAX_CAMKES_MSGQUEUE_ID) {
        ZF_LOGE("Trying to retrieve a channel with an ID greater than the maximum ID");
        return NULL;
    }

    if (role == MSGQUEUE_UNASSIGNED) {
        ZF_LOGE("Trying to retrieve an uninitialised channel");
        return NULL;
    }

    if (camkes_msgqueue_channels[msgqueue_id].role != role) {
        ZF_LOGE("Requested msgqueue channel doesn't match the role passed in");
        return NULL;
    }

    return &camkes_msgqueue_channels[msgqueue_id];
}
