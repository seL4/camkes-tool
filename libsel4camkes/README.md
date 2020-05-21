<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# libsel4camkes

This is a library that contain a collection of user-friendly abstractions to
the CAmkES runtime environment, as well some backend functions for the CAmkES
environment to bootstrap and configure the runtime environment.

## Usage

All CAmkES components link against this library, but if there is a specific
need to link against this library, include this library using the
`target_link_library` CMake directive or similar with the `sel4camkes` item.

## Contents

The functions exposed by this library can be found in the `include` folder.
There is also more in-depth documentation inside the `docs` folder.
