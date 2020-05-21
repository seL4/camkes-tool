<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# Dataport

libsel4camkes provides some functions for interacting with CAmkES dataports.
There are also some definitions intended for CAmKES internal use.

## Usage

There are two functions for wrapping and unwrapping pointers that point to the
dataport into and from a data format that can be shared between components. These are:

```c
dataport_ptr_t dataport_wrap_ptr(void *ptr);

void *dataport_unwrap_ptr(dataport_ptr_t ptr);
```

Although components may share some memory between each with the use CAmkES
dataports, the dataports may not be necessarily be mapped into the same virtual
address in the components' address space. Thus, these functions are used to
communicate pointers in the dataport by converting in a format that's
understood by all components that have a shared dataport connection.

There is also an addditional function that allows clients to perform cache
maintaince operations on the dataports.

```c
int camkes_dataport_flush_cache(size_t start_offset, size_t size,
                                uintptr_t dataport_start, size_t dataport_size,
                                dma_cache_op_t cache_op);
```
