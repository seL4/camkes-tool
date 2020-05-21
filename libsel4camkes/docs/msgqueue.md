<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Message queues

`libsel4camkes` provides an implementation of a message queue transport
mechanism. The message queues can be used to transfer small messages from a
component to another component asynchronously. The message size is limited by
the underlying `virtqueue` mechanism and the fact that the messages are copied.
For large messages, it is recommended to use shared memory/data ports directly.
Small message transfer is especially useful, when additional state needs to be
passed instead of a simple alert like the notifications that seL4 provides. Note
that message queues are one-way and not a two-way channel, can only be one
sender and one receiver per channel.

## Usage

The message queue libraries require components to first initialise a
`seL4Msgqueue` CAmkES connection between components. Here's an example of how
this is done:

```c
component Foo {
    dataport Message rx;
}

component Foo2 {
    dataport Message tx;
}

assembly {
    composition {
        component Foo bar;
        component Foo2 baz;

        connection messagequeue_foo seL4Msgqueue(from baz.tx, to bar.rx);
    }

    configuration {
        bar.rx_id = 1;
        baz.tx_id = 1;
        messagequeue_foo.queue_size = 256;
    }
}
```

From the example above, the sender is `baz`, and the receiver is `bar`. The IDs
of this particular message queue channel are 1 for both components. It is
possible to have multiple channels for a component, but their IDs must be
different. The queue size of the message queue is 256 and can be changed. It
must be a power of two. The messages that will be transferred in the channel are
of type `Message` as indicated by the dataport.

Next, in the application code, the sender and receivers must initialise their
ends of the channel by calling the appropriate function from the following:

```c
int camkes_msgqueue_sender_init(int msgqueue_id, camkes_msgqueue_sender_t *sender);

int camkes_msgqueue_receiver_init(int msgqueue_id, camkes_msgqueue_receiver_t *receiver);
```

The sender can then call the following function to send messages.

```c
int camkes_msgqueue_send(camkes_msgqueue_sender_t *sender, void *message, size_t message_size);
```

The message type should be of the type of the underlying dataport, there are
checks to make sure that the message size does not go over the limit defined in
`camkes_msgqueue_sender_t`.

On the receiver side, there are two functions to check the status of the channel
and to possibly block on the channel waiting for a message.

```c
int camkes_msgqueue_poll(camkes_msgqueue_receiver_t *recevier);

int camkes_msgqueue_wait(camkes_msgqueue_receiver_t *receiver);
```

When a message arrives as indicated by the functions, the receiver can retrieve
a message of the channel with the following.

```c
int camkes_msgqueue_get(camkes_msgqueue_receiver_t *receiver, void *buffer, size_t buffer_size);
```

The buffer should be sufficiently sized to store a message of a type as
indicated by the type of the dataport.
