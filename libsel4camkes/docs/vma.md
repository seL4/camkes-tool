<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: BSD-2-Clause
-->

# VMA

This part of the library contains definitions that can be used to obtain
information about the Virtual Memory Areas (VMA) of a CAmkES application. The
defintions are mostly used by other parts of the library to manipulate a
component's address space.

## Usage

Information about the sections of a component's address space can be found via
the following variable.

```c
extern const struct camkes_vma camkes_vmas[];
```

This array is filled in by the CAmkES backend as it generates code for a
particular component.
