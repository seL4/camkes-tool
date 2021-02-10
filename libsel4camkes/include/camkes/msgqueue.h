/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <virtqueue.h>

#include <sel4/sel4.h>

typedef struct camkes_msgqueue_sender {
    bool initialised;
    virtqueue_driver_t sender_channel;
    size_t message_size;
} camkes_msgqueue_sender_t;

typedef struct camkes_msgqueue_receiver {
    bool initialised;
    virtqueue_device_t receiver_channel;
    size_t message_size;
    int (*poll)(void);
    void (*wait)(void);
} camkes_msgqueue_receiver_t;

int camkes_msgqueue_sender_init(int msgqueue_id, camkes_msgqueue_sender_t *sender);

int camkes_msgqueue_receiver_init(int msgqueue_id, camkes_msgqueue_receiver_t *receiver);

int camkes_msgqueue_send(camkes_msgqueue_sender_t *sender, void *message, size_t message_size);

int camkes_msgqueue_poll(camkes_msgqueue_receiver_t *receiver);

int camkes_msgqueue_wait(camkes_msgqueue_receiver_t *receiver);

int camkes_msgqueue_get(camkes_msgqueue_receiver_t *receiver, void *buffer, size_t buffer_size);
