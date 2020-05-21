<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# Virtqueues

libsel4camkes provides an implementation of the virtqueue transport mechanism.
virtqueues can be used to asynchronously transfer data between two components.
Although virtqueues are mostly used between clients and device drivers, this
transport mechanism is useful for general producer-consumer patterns.

## Usage

The virtqueue libraries requires components to first initialise a
`seL4VirtQueue` CAmkES connection between components. Here's an example of how
this is done:

```c
component Foo {
    uses VirtQueueDrv drv;
}

component Foo2 {
    uses VirtQueueDev dev;
}

assembly {
    composition {
        component VirtQueueInit vq_init;
        component Foo bar;
        component Foo2 baz;
        
        connection virtqueue_foo seL4VirtQueue(to vq_init.init, from bar.drv, from baz.dev);
    }
    
    configuration {
        bar.drv_id = 1;
        baz.dev_id = 1;
        bar.drv_shmem_size = 4096;
        baz.dev_shmem_size = 4096;
        virtqueue_foo.init_topology = [{"drv" : "bar.drv", "dev": "baz.dev" }];
    }
}
```

From the example above, the driver side of the virtqueue is `bar` and the
device side is `baz`. The IDs of this particular virtqueue channel is 1 for
both components. It is possible to have multiple channels for a component, but
each channel's ID must be different. The memory size of the channel is 4096 and
can also be changed, however, it must be page-aligned to 4096.

Next, in the application code, the driver and device side of the channel must
initialise their end of the channel by calling the appropriate function from
the following:

```c
static inline int camkes_virtqueue_driver_init(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id) { ... }

static inline int camkes_virtqueue_device_init(virtqueue_device_t *device, unsigned int camkes_virtqueue_id) { ... }
```

There is also a version of these functions which can return the underlying
notification object that is backing the notification part of the virtqueues.

```c
int camkes_virtqueue_driver_init_with_recv(virtqueue_driver_t *driver, unsigned int camkes_virtqueue_id, 
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge);
                                           
int camkes_virtqueue_device_init_with_recv(virtqueue_device_t *device, unsigned int camkes_virtqueue_id,
                                           seL4_CPtr *recv_notification, seL4_CPtr *recv_badge);
```

The rest of the functions are essentially helper or convenience functions over
the virtqueue interface as defined
[here](https://github.com/SEL4PROJ/projects_libs/blob/master/libvirtqueue/include/virtqueue.h).

### Driver

When sending data over to the device side, it is preferred to use to these two functions.

```c
int camkes_virtqueue_driver_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size);

int camkes_virtqueue_driver_scatter_send_buffer(virtqueue_driver_t *vq, void *buffer, size_t size);
```

When collecting buffers from the device side, the client must first obtain a
handle to a used buffer ring via this virtqueue interface function:

```c
int virtqueue_get_used_buf(virtqueue_driver_t *vq, virtqueue_ring_object_t *robj, uint32_t *len);
```

It is then possible to gather each buffer in the used buffer ring and copy it into a larger buffer uisng the first function or iterate through each buffer in the ring using the second function:

```c
int camkes_virtqueue_driver_gather_copy_buffer(virtqueue_driver_t *vq, virtqueue_ring_object *handle,
                                        void *buffer, size_t size);
                                        
int camkes_virtqueue_driver_gather_buffer(virtqueue_driver_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag);
```

### Device side

Collecting buffers from the driver side requires the client to first obtain a
handle to an available buffer ring via this virtqueue interface function:

```c
int virtqueue_get_available_buf(virtqueue_device_t *vq, virtqueue_ring_object_t *robj);
```

The buffers can then be:
    - gathered and copied into a larger buffer using the first function,
    - have the contents of a larger scatter-copied into the buffers using the second function,
    - or, iterated through using the second function:

```c
int camkes_virtqueue_device_gather_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                               void *buffer, size_t size);
                                               
int camkes_virtqueue_device_scatter_copy_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                                void *buffer, size_t size);
                                                
int camkes_virtqueue_device_gather_buffer(virtqueue_device_t *vq, virtqueue_ring_object_t *handle,
                                          void **buffer, unsigned *size, vq_flags_t *flag);
```

Note that the first two buffers, will automatically add the buffers to the
device channel's used ring for the driver side to collect; the third one will
not.
