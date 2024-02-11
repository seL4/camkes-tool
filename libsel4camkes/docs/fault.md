<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Fault

`libsel4camkes` provides functions for examining faults that are generated
by applications.

## Usage

When an application triggers a fault, the seL4 kernel will invoke the the
faulting thread's fault handler. The fault handler is then given information
about the fault and is expected to resolve the situation. CAmkES will register a
default fault handler on a debug build that will call a function to show
information about the fault. This function is:

```c
void camkes_show_fault(seL4_MessageInfo_t info, seL4_CPtr thread_id,
                       const char *name, bool tcp_caps_available,
                       const camkes_memory_region_t *memory_map);
```

The function takes the fault information that the kernel provides in the
faulting thread's IPC buffer and displays it in a human readable format.

Currently this function is expected to be called by a component's fault handler
if any component threads fault.
