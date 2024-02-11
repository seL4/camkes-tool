<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# DMA

`libsel4camkes` provides functions for interacting with a DMA pool that is
allocated and managed by CAmkES. These functions are essentially an
implementation of the `ps_dma_man_t` interface in `ps_io_ops_t`. It is preferred
that the DMA requests go through the `ps_dma_man_t` interfaces instead of using
these functions.

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
