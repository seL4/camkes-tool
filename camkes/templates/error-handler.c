/*# We expect the following variables to be defined when this fragment is
 *# included.
 #*/
/*? assert(isinstance(interface, str)) ?*/     /*# Name of this interface #*/
/*? assert(isinstance(error_handler, str)) ?*/ /*# Symbol to use for creating error handler #*/

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
