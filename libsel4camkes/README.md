<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# libsel4camkes

This is a library that contains a collection of user-friendly abstractions to
the CAmkES runtime environment, as well some backend functions for the CAmkES
environment to bootstrap and configure the runtime environment.

## Usage

All CAmkES components link against this library, but if there is a specific
need to link against this library, include this library using the
`target_link_library` CMake directive or similar with the `sel4camkes` item.

## Contents

The functions exposed by this library can be found in the `include` folder.
There is also more in-depth documentation inside the `docs` folder.
