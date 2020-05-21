<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# Syscalls

While the CAmkES runtime isn't fully POSIX compliant (and does not intend to
be), the CAmkES runtime implements a subset of POSIX syscalls to provide some
compatibility with POSIX applications. The
[header](https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/include/camkes/syscalls.h)
provides a list of syscalls that the CAmkES runtime implements.
