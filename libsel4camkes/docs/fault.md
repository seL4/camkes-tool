<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# Fault

libsel4camkes provides some functions for examining faults that are generated
by the applications.

## Usage

When an application triggers a fault, the seL4 kernel will invoke the
applications, or more specifically, the thread's fault handler. The fault
handler is then given information about the fault and is expected to resolve
the situation. CAmkES will register a default fault handler on a debug build
that will call a function to show information about the fault. This function is:

```c
void camkes_show_fault(seL4_MessageInfo_t info, seL4_CPtr thread_id,
                       const char *name, bool tcp_caps_available,
                       const camkes_memory_region_t *memory_map);
```

The function takes the fault information written by the kernel into the
faulting thread's IPC buffer and displays it in a human readable format.

Currently this function is expected to be called by a component's fault handler
if any component threads fault.
