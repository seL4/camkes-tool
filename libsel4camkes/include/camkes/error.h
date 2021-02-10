/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Error handling API for CAmkES. */

#pragma once

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/* Types of errors that can occur in CAmkES glue code. */
typedef enum {

    /* No error occurred. Used to indicate normal operation. */
    CE_NO_ERROR = 0,

    /* During marshalling, the next operation if we were to continue would
     * exceed the size of the target buffer. Note that continuing in the event
     * of such an error *will* cause an out-of-bounds memory write.
     */
    CE_BUFFER_LENGTH_EXCEEDED,

    /* In an RPC communication, the method index indicated by the caller was
     * out of range for the given interface. That is, the method index was
     * larger than the number of methods in this interface, or it was negative.
     */
    CE_INVALID_METHOD_INDEX,

    /* The payload of an RPC (marshalled parameters) was somehow invalid. This
     * includes cases where an IPC recipient received a message that was either
     * too long or too short for what it was expecting.
     */
    CE_MALFORMED_RPC_PAYLOAD,

    /* A system call that is never expected to fail in normal operation, did
     * so. Recovery actions are most likely dependent on what and where the
     * actual failure was.
     */
    CE_SYSCALL_FAILED,

    /* Some internal memory/bookkeeping allocation the glue code needed to
     * perform did not complete successfully. It will be difficult to diagnose
     * the cause of one of these without looking at the location at which the
     * error was triggered.
     */
    CE_ALLOCATION_FAILURE,

    /* A counter would overflow or underflow if execution were to continue from
     * the current point.
     */
    CE_OVERFLOW,

} camkes_error_type_t;

/* Tagged union representing data about an error itself. */
typedef struct {
    /* The type of the error. This tag determines which member of the union
     * below is relevant.
     */
    camkes_error_type_t type;

    /* The component instance in which this error occurred. This will probably
     * never be ambiguous programmatically, but it may be useful to have this
     * value available to print. Error handlers can assumes this pointer will
     * never be NULL.
     */
    const char *instance;

    /* The interface in which this error occurred. If this error occurred in a
     * component-global context then this pointer will be NULL.
     */
    const char *interface;

    /* The source code position at which the error occurred. Useful if you are
     * debugging template generation.
     */
    const char *filename;
    long lineno;

    /* A human readable description of the failure. Error handlers can assume
     * this pointer will never be NULL.
     */
    const char *description;

    union {
        /* No union member for CE_NO_ERROR. */

        struct { /* CE_BUFFER_LENGTH_EXCEEDED */

            /* The current byte offset into the buffer. */
            unsigned current_length;

            /* The byte offset we're about to reach if we perform the next
             * write. I.e. an offset out-of-bounds of the buffer itself.
             */
            unsigned target_length;
        };

        struct { /* CE_INVALID_METHOD_INDEX */

            /* The range of valid method indices. */
            uint64_t lower_bound;
            uint64_t upper_bound;

            /* The value that caused this error. */
            uint64_t invalid_index;
        };

        struct { /* CE_MALFORMED_RPC_PAYLOAD */

            /* The (possibly invalid) length of the payload. */
            unsigned length;

            /* The current byte offset into the buffer. I.e. the point at which
             * we realised we had an invalid payload.
             */
            unsigned current_index;
        };

        struct { /* CE_SYSCALL_FAILED */

            /* The syscall that we ran. This value will be a member of
             * invocation_label or arch_invocation_label from libsel4.
             */
            int syscall;

            /* The error value returned by seL4. */
            int error;
        };

        struct { /* CE_ALLOCATION_FAILURE */

            /* The number of bytes that was being allocated when the failure
             * occurred. This field may be zero if the amount was not relevant.
             */
            size_t alloc_bytes;
        };
    };
} camkes_error_t;

/* The action to take to recover from an error. An error handler, as described
 * below, should return one of these values to indicate what action the glue
 * code should take.
 */
typedef enum {

    /* Used as a sentinel for a context where an action is invalid. Don't ever
     * return this from an error handler.
     */
    CEA_INVALID = -1,

    /* Terminate the currently running piece of glue code by returning. If the
     * offending code was called from a glue code event loop, this generally
     * means return to the event loop. If the offending code was called from
     * user code, this means return to user code where the calling function is
     * expected to be aware (by some out-of-band communication) that an error
     * has occurred.
     */
    CEA_DISCARD,

    /* Ignore the error and continue. This is generally dangerous and not what
     * you want.
     */
    CEA_IGNORE,

    /* Exit with failure in the current thread. Note that what 'exit' means
     * here depends on a number of things including whether the thread has a
     * cap to itself.
     */
    CEA_ABORT,

    /* Exit with failure and also try to halt the entire system if possible.
     * This action implies CEA_ABORT and only differs on a debug kernel where
     * it is possible to stop the system. If you have no error handlers
     * installed, this is the default action.
     */
    CEA_HALT,

} camkes_error_action_t;

/* An error handling function. If components define their own error handlers,
 * they should conform to this prototype. The argument is the error that
 * occurred and the return value is the recovery action the glue code should
 * take.
 */
typedef camkes_error_action_t (*camkes_error_handler_t)(camkes_error_t *);

/* Register a component-global error handler. More fine-grained registration
 * functions (one per-interface) are generated and prototyped in the generated
 * header. Errors that occur in interface glue code will only invoke this error
 * handler if no error handler is registered for the interface itself. This
 * registration function returns a pointer to the old handler.
 */
camkes_error_handler_t camkes_register_error_handler(
    camkes_error_handler_t handler);

/* Throw an error from glue code. This function is not expected to be called by
 * user code.
 */
camkes_error_action_t camkes_error(camkes_error_t *e) COLD;

/* Convenience for using halt() inside macro definitions. This is not expected
 * to be called from user code. Note that it does not halt on a non-debug
 * kernel.
 */
#ifdef CONFIG_DEBUG_BUILD
#define halt() seL4_DebugHalt()
#else
#define halt() do { } while (0)
#endif

#ifdef CONFIG_CAMKES_ERROR_HANDLER_CONFIGURABLE

/* Convenience macro for throwing an error from glue code.
 *  handler - A camkes_error_handler_t to invoke.
 *  edata - Error structure to throw to the error handler.
 *  action - Action to take on return of CEA_DISCARD from the error
 *    handler. This should be a GNU statement expression (aka compound
 *    statement).
 */
#define ERR(handler, edata, action) ({ \
            COLD_PATH(); \
            camkes_error_t _e = edata; \
            _e.filename = __FILE__; \
            _e.lineno = __LINE__; \
            switch (handler(&_e)) { \
                case CEA_DISCARD: \
                    action; \
                    UNREACHABLE(); \
                case CEA_IGNORE: \
                    break; \
                case CEA_HALT: \
                    halt(); \
                    /* If we return we'll just fall through. */ \
                case CEA_ABORT: \
                    abort(); \
                    /* In case we return */ \
                    while(1); \
                default: \
                    UNREACHABLE(); \
            } \
        })

#elif defined(CONFIG_CAMKES_ERROR_HANDLER_GUARD)

#define ERR(handler, edata, action) GUARD(false)

#elif defined(CONFIG_CAMKES_ERROR_HANDLER_ABORT)

#define ERR(handler, edata, action) abort()

#elif defined(CONFIG_CAMKES_ERROR_HANDLER_DISCARD)

#define ERR(handler, edata, action) action

#else

#error no error handling mode defined

#endif

#ifdef CONFIG_CAMKES_ERROR_HANDLER_GUARD

#define ERR_IF(cond, handler, edata, action) GUARD(!(cond))

#else

/* Conditionally throw an error. */
#define ERR_IF(cond, handler, edata, action) ({ \
            if (unlikely(cond)) { \
                ERR(handler, edata, action); \
            } \
        })

#endif
