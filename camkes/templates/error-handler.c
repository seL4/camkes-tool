/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(interface, six.string_types)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(error_handler, six.string_types)) ?*/ /*# Symbol to use for creating error handler #*/

/* The currently active error handler. This variable is marked UNUSED to squash
 * compiler warnings generated when the user's build configuration causes the
 * two following functions to be pruned from the final source.
 */
static camkes_error_handler_t /*? error_handler ?*/_fn UNUSED;

camkes_error_handler_t /*? interface ?*/_register_error_handler(
    camkes_error_handler_t handler) {
    camkes_error_handler_t old = /*? error_handler ?*/_fn;
    /*? error_handler ?*/_fn = handler;
    return old;
}

static camkes_error_action_t UNUSED /*? error_handler ?*/(camkes_error_t *error) {
    if (/*? error_handler ?*/_fn == NULL) {
        /* No registered handler; invoke the generic error handler. */
        return camkes_error(error);
    }
    return /*? error_handler ?*/_fn(error);
}
