<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Syscalls

While the CAmkES runtime isn't fully POSIX compliant (and does not intend to
be), the CAmkES runtime implements a subset of POSIX syscalls to provide some
compatibility with POSIX applications. The
[header](https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/include/camkes/syscalls.h)
provides a list of syscalls that the CAmkES runtime implements.
