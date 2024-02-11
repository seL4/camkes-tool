<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Error

`libsel4camkes` provides some functions for dealing with errors from the CAmkES
runtime.

## Usage

In rare occasions, the CAmkES runtime can produce an error on some operations.
When such an error occurs, the CAmkES runtime will invoke an error handler to
deal with the error. The default error handler will simply halt the system. It
is possible to install a custom error handler with the following function.

```c
camkes_error_handler_t camkes_register_error_handler(camkes_error_handler_t handler);
```

The error handler is of type:

```c
typedef camkes_error_action_t (*camkes_error_handler_t)(camkes_error_t *);
```

The error handler is given relevant information from the `camkes_error_t`
struct and is expected to handle the error and return a `camkes_error_type_t`
return code indicating the action to take. The actions that can be taken are to:

- discard the transaction
- ignore the error
- exit with failure

See the
[header](https://github.com/seL4/camkes-tool/blob/master/libsel4camkes/include/camkes/error.h)
for more information.
