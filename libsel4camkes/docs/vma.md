<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VMA

This part of the library contains definitions that can be used to obtain
information about the Virtual Memory Areas (VMA) of a CAmkES application. The
definitions are mostly used by other parts of the library to manipulate a
component's address space.

## Usage

Information about the sections of a component's address space can be found via
the following variables.

```c
extern const struct camkes_vma camkes_vmas[];

extern const size_t camkes_vmas_size;
```

This array is filled in by the CAmkES backend as it generates code for a
particular component.
