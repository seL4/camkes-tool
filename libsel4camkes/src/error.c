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

#include <camkes/error.h>
#include <stdio.h>
#include <utils/util.h>
#include <inttypes.h>

/* The default error handler that is invoked if no other error handler is
 * registered.
 */
static camkes_error_action_t default_error_handler(camkes_error_t *error) {
    fprintf(stderr, "-- %s --\n", error->instance);
    switch (error->type) {

        case CE_BUFFER_LENGTH_EXCEEDED:
            fprintf(stderr, "Error: about to exceed buffer length by writing "
                "up to %u bytes\n", error->target_length);
            break;

        case CE_INVALID_METHOD_INDEX:
            fprintf(stderr, "Error: invalid method index of %"PRIu64"\n",
                error->invalid_index);
            break;

        case CE_MALFORMED_RPC_PAYLOAD:
            fprintf(stderr, "Error: Malformed RPC payload\n");
            break;

        case CE_SYSCALL_FAILED:
            fprintf(stderr, "Error: syscall failed\n");
            break;

        case CE_ALLOCATION_FAILURE:
            fprintf(stderr, "Error: allocation failed\n");
            break;

        default:
            UNREACHABLE();
    }
    fprintf(stderr, "Occurred at %s:%lu\n", error->filename, error->lineno);
    fprintf(stderr, "Details: %s\n", error->description);

    return CEA_HALT;
}

/* Currently active error handler. */
static camkes_error_handler_t err = default_error_handler;

camkes_error_action_t camkes_error(camkes_error_t *e) {
    return err(e);
}

camkes_error_handler_t camkes_register_error_handler(camkes_error_handler_t handler) {
    camkes_error_handler_t old = err;
    err = handler;
    return old;
}
