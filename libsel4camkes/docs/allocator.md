<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Allocator

The allocator in `libsel4camkes` can be used to allocate seL4 capability objects
from a managed pool. The `camkes_provide` function is mostly used by the
CAmkES backend to setup the pool on behalf of the user. In `simple` or
'dynamic' configurations of CAmkES, other allocators (`vka`, `vspace`, etc)
would be preferred instead.

## Usage

The `camkes_alloc` and `camkes_free` functions can be used to allocate and free
seL4 capability objects from and to the managed pool. It is possible to provide
your own seL4 objects to the pool using `camkes_provide` but CAmkES allows
users to specify some objects to be created and provided to the pool
automatically.

So far, only TCBs, Endpoints, Notifications, and Untypes can be allocated.
Below is an example of asking CAmkES to allocate these objects.

```c
assembly {
    composition {
        component Foo bar;
    }

    configuration {
        bar.<object type>_pool = 12;
    }
}
```

In the example, CAmkES would allocate 12 objects of type 'object type'. Valid
object types are:

- `tcb`
- `ep`
- `notification`
- `untypedX`, where X is a number indicating the size of the untyped, e.g.
  `untyped12` would ask for untypes of size 2 to the power 12, or 4096
