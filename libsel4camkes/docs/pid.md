<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# PID

This is a constant variable that tracks the ID of the CAmkES component.
Although CAmkES or seL4 does not have a concept of processes, these variable is
used to maintain compatibility with parts of the POSIX standard. Note that the
variable is managed by CAmkES-generated code.

TODO Check this?
