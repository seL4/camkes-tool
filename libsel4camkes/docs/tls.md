<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Thread-Local Storage (TLS)

This part of the library contains definitions and functions related to
CAmkES-specific thread-local storage. These functions are intended for
CAmkES-internal use to manage the state of each thread on top of the CAmkES
runtime.

## Usage

When constructing templates for RPC-related CAmkES-connections, there may be
situations where the seL4 endpoint reply cap may need to be managed. There are
three functions which can be used to manage the reply cap, these are:

```c
int camkes_declare_reply_cap(seL4_CPtr shadow_slot);

void camkes_protect_reply_cap(void);

seL4_Error camkes_unprotect_reply_cap(void);
```
