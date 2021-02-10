/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/msgqueue.h>

#define MAX_CAMKES_MSGQUEUE_ID 100

typedef enum msgqueue_role {
    MSGQUEUE_UNASSIGNED,
    MSGQUEUE_SENDER,
    MSGQUEUE_RECEIVER,
} msgqueue_role_t;

typedef struct camkes_msgqueue_channel {
    msgqueue_role_t role;
    void *buffer;
    unsigned queue_len;
    size_t buffer_size;
    size_t message_size;
    union {
        /* These will be filled in if the channel's role is "MSGQUEUE_RECEIVER" */
        struct {
            int (*poll)(void);
            void (*wait)(void);
        } receiver_funcs;
        /* Similarly, if the channel's role is "MSGQUEUE_SENDER", this should be filled in */
        struct {
            void (*notify)(void);
        } sender_funcs;
    };
} camkes_msgqueue_channel_t;

int camkes_msgqueue_channel_register_sender(int msgqueue_id, void *buffer, unsigned queue_len, size_t buffer_size,
                                            size_t message_size, void (*notify)(void));

int camkes_msgqueue_channel_register_receiver(int msgqueue_id, void *buffer, unsigned queue_len, size_t buffer_size,
                                              size_t message_size, int (*poll)(void), void (*wait)(void));

camkes_msgqueue_channel_t *camkes_msgqueue_channel_get(int msgqueue_id, msgqueue_role_t role);
