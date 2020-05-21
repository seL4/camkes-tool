<!--
  Copyright 2020, Data61
  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
  ABN 41 687 119 230.

  This software may be distributed and modified according to the terms of
  the BSD 2-Clause license. Note that NO WARRANTY is provided.
  See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
  -->

# Error

libsel4camkes provides some functions for dealing with errors with the CAmkES
runtime.

## Usage

In rare occasions, the CAmkES runtime can fail on some operations. Upon
failure, the CAmkES runtime will invoke an error handler to deal with the
error. The default error handler will simply halt the system upon error. It is
possible to install a custom error handler with the following function.

```c
camkes_error_handler_t camkes_register_error_handler(camkes_error_handler_t handler);
```

The error handler is of type:

```c
typedef camkes_error_action_t (*camkes_error_handler_t)(camkes_error_t *);
```

The error handler is given relevant information from the `camkes_error_t`
struct and is expected to handle the error and return a `camkes_error_type_t`
return code indicating the action to take. The actions that can be taken are:
    - to discard the transaction
    - ignore the error
    - exit with failure

See the [header](https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/include/camkes/error.h) for more information.
