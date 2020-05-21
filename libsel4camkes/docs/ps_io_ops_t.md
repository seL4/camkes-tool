<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->
  
# `ps_io_ops_t`

CAmkES provides an implementation of the `ps_io_ops_t` as part
of its runtime environment.

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/include/camkes/io.h>

## `ps_malloc_ops_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/io.c>

The CAmkES `ps_malloc_ops_t` interface for performing anonymous memory
allocation is implemented by wrapping musllibc `malloc`, `calloc` and `free`
calls. A CAmkES component can be configured with a fixed sized heap that is
used to perform these memory allocations.

## `ps_io_mapper_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/io.c>

The CAmkES `ps_io_mapper_t` interface for memory mapped I/O (MMIO) uses a
record of all device memory mappings in the component's virtual address space
to look up a virtual address for a corresponding physical address.  CAmkES
hardware connector templates generate the MMIO mappings in the CapDL spec. They
are also expected to register the mappings in the special linker section
`_dataport_frames`, describing an MMIO mapping region by its size, physical
address and mapping attributes. The CAmkES `ps_io_mapper_t` uses this
information to return the mapping information to callers.

No action is taken when the `unmap` function is called.

Mapping attributes requested are currently ignored since the mappings already
exist and cannot be changed. A configuration may be provided in the future to
perform mapping attribute validation in order to catch any configuration
errors, but this is currently unsupported.

## `ps_dma_man_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/dma.c>

The CAmkES `ps_dma_man_t` interface for Direct Memory Access (DMA) uses a
statically defined pool of DMA memory from which the interface implementation
allocates DMA regions. The mappings for this pool are created during system
initialisation and the interface responds to alloc and pin requests by handing
out the virtual and physical addresses for these regions.

Hardware memory management mechanisms (such as IOMMU or SMMU) are not currently
supported, but this will be implemented by also mapping the static DMA pool
memory into the hardware address spaces provided by the IOMMU implementation.

The cache operations provided by this interface are no-ops as the entire pool
is mapped uncached.

The size of the DMA pool is configured for each component by setting
`${component_name}.dma_pool = ${pool_size_in_bytes};` in the `configuration`
section of a `.camkes` file.

## `ps_irq_ops_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/irq.c>

The CAmkES `ps_irq_ops_t` interface for hardware interrupt handling uses a
record of interrupt to seL4 notification mappings to register callback handlers
for specific interrupts. When a CAmkES connector allocates an seL4 notification
as a specific interrupt handler it records information in the `_allocated_irqs`
linker section. The CAmkES `ps_irq_ops_t` implementation looks through this
section to match a requested register call with an existing interrupt
notification. CAmkES then sets the provided callback handler to be invoked when
an interrupt arrives on the notification. When an interrupt is received, the
provided handler is invoked and given a function for performing the seL4
interrupt acknowledgment as the interface ACK function.

## `ps_io_port_ops_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/io.c>

The `ps_io_port_ops_t` interface for architectural I/O operations is
implemented for x86 IOPorts. Connectors that allocate CapDL IOPort capabilities
are expected to register these capabilities in the `_ioport_regions` linker
section. The CAmkES imlementation of the IOPort interface looks up these
capabilities for requested IOPorts and then performs the correct seL4 IOPort
invocation. Errors are returned for any IOPorts that the component does not
have access to. 

A feature may be added in the future for delegating IOPort calls to a different
CAmkES component. This is required to support sharing of devices across
components such as for a PCI bus. Currently, IOPort operations for accessing
PCI configuration IOPorts located in a different components need to be called
through a separate API.

## `ps_io_fdt_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/io.c>

The CAmkES `ps_io_fdt_t` interface for providing access to a flattened device
tree (FDT) uses node information made available in the component's address
space during system initialisation.  CAmkES hardware connectors register a
CapDL FDT fill-frame that causes the FDT (which is passed into CapDL loader by
seL4 during startup) to be copied into the component's address space. The
CAmkES `ps_io_fdt_t` interface returns a reference to this FDT.

## `ps_interface_registration_ops_t`

<https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/src/interface_registration.c>

The CAmkES `ps_interface_registration_ops_t` interface is implemented as a
two-level nested linked list data structure that can have elements appended and
removed while also allowing iteration over it.

CAmkES populates the list for each component based on which other components it
is connected to according the static system architecture.

