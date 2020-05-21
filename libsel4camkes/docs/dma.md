<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# DMA

libsel4camkes provides some functions for interacting with a DMA pool that
CAmkES allocates and manages. These functions are essentially an implementation
of the `ps_dma_man_t` interface in `ps_io_ops_t`. It is preferred that the DMA
requests go through the `ps_dma_man_t` interfaces instead of using these
functions.

## Usage

Each DMA pool is unique to each component and can be allocated by setting a
specific attribute in CAmkES. For example, the following allocates a DMA pool
that's of size `0x4000` to the component `bar`.

```c
assembly {
    composition {
        component Foo bar;
    }
    
    configuration {
        bar.dma_pool = 0x4000;
    }
}
```

CAmkES will then ask the linker to provide a section of memory to be reserved
as the DMA pool. During component initialisation, the CAmkES runtime will
initialise the DMA pool by calling `camkes_dma_init` with the reserved DMA
pool. Clients can then call `camkes_dma_alloc` and `camkes_dma_free`, or use
the functions exposed by the `ps_dma_man_t` interface after a `camkes_io_ops`
call to interact with the DMA pool.
