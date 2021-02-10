<!--
     Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# CAmkES support functionality

To use this library in a project you should link 'sel4camkes' to your target
application/component with CMake. This library provides various utilities for
interfacing with seL4 in a CAmkES-based system. Some of these utilities are:

### virtqueue

**_This implementation is currently a work in progress_**

Functions are provided to help create virtqueue connections between your CAmkES
components. This is based on the libvirtqueue implementation
(project_libs/libvirtqueue). The functions provided are divided into two
interfaces, being:
    * _virtqueue template.h:_ These are functions intended to be used by a
    CAmkES template. This interface is meant to allow a CAmkES template to
    register a virtqueue channel.
    * _virtqueue.h_ : These are functions intended to be used by a CAmkES
    component. This interface provides a CAmkES component the ability to
    create virtqueue objects (from libvirtqueue) out of the channels
    registered by its templates. This interface also includes
    memory allocation mechanisms over dataports for creating virtqueue buffers
    to pass data with.

#### Caveats

This library is still under active development. Current shortcomings of the
implementation include:
* Each virtqueue is expected to have its own shared memory buffer region. Thus
  allocating a virtqueue buffer will always return the same region of memory. The
  allocation mechanisms are intended to be changed to work over a global memory region with
  other components.
* The maximum number of virtqueues a component can register is defined by `MAX_CAMKES_VIRTQUEUE_ID`
