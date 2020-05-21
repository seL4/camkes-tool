<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
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
