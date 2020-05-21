<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Init

The init functions in `libsel4camkes` are mostly used internally in the CAmkES
runtime backend. These functions are the entry points for the component's
control thread, which sets up the runtime and prepares the state for running
the component's application code.
