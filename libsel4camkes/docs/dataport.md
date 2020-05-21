<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Dataport

`libsel4camkes` provides some functions for interacting with CAmkES dataports.
There are also some definitions intended for CAmKES internal use.

## Usage

There are two functions for wrapping and unwrapping pointers that point to the
dataport into and from a data format that can be shared between components.
These are:

```c
dataport_ptr_t dataport_wrap_ptr(void *ptr);

void *dataport_unwrap_ptr(dataport_ptr_t ptr);
```

Although components may share memory between each other using CAmkES
dataports, the dataports may not be necessarily be mapped into the same virtual
address in the components' address space. Thus, these functions are used to
communicate pointers in the dataport by converting them into a format that's
understood by all components that have a shared dataport connection.

There is an additional function that allows clients to perform cache
maintenance operations on the dataports.

```c
int camkes_dataport_flush_cache(size_t start_offset, size_t size,
                                uintptr_t dataport_start, size_t dataport_size,
                                dma_cache_op_t cache_op);
```
