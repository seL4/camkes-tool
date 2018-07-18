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

/*- import 'helpers/error.c' as error with context -*/
/*- import 'helpers/array_check.c' as array_check with context -*/
/*- import 'helpers/marshal.c' as marshal with context -*/
/*- from 'helpers/tls.c' import make_tls_symbols -*/

#include <sel4/sel4.h>
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/dataport.h>
#include <camkes/error.h>
#include <camkes/timing.h>
#include <camkes/tls.h>
#include <sync/sem-bare.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*# HACK: The CapDL verification is based on a future, proposed version of
 *# seL4, wherein only Write is required on an endpoint to send to it. This
 *# allows a more principled information flow analysis. The obvious question is,
 *# why not use seL4RPCCall, a connector which already does not require Read on
 *# the sender's side? The answer is that this connector requires Grant, which,
 *# in the access control model puts sender and receiver in the same domain
 *# which is the exact opposite of what we want.
 *#
 *# To get around this mess, we detect if the user is targeting the CapDL
 *# verification and, if so, do not provide Read on this capability. Note that
 *# the resulting system will not run correctly.
 #*/
/*- if os.environ.get('CONFIG_CAMKES_LABEL_MAPPING', '') == 'y' -*/
  /*- set read = False -*/
/*- else -*/
  /*- set read = True -*/
/*- endif -*/
/*- set ep = alloc('ep', seL4_EndpointObject, read=read, write=True) -*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.interface.type.methods) -*/
/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/
/*- set threads = list(six.moves.range(1, 2 + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes))) -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*? error.make_error_handler(interface, error_handler) ?*/

/*- if not options.frpc_lock_elision or 1 + len(me.instance.type.provides) + len(me.instance.type.consumes) > 1 -*/
    /*# See below for an explanation of this conditional. #*/
    /*- set lock_ep = alloc('lock', seL4_EndpointObject, read=True, write=True) -*/
    /*- set lock = c_symbol('lock') -*/
    static volatile int /*? lock ?*/ = 1;
/*- endif -*/

TIMING_DEFS(/*? me.interface.name ?*/, "glue code entry", "lock acquired", "marshalling done", "communication done", "lock released", "unmarshalling done")

/*? array_check.make_array_typedef_check_symbols(me.interface.type) ?*/

int /*? me.interface.name ?*/__run(void) {
    /* This function is never actually executed, but we still emit it for the
     * purpose of type checking RPC parameters.
     */
    UNREACHABLE();

    /*# Check any typedefs we have been given are not arrays. #*/
    /*? array_check.perform_array_typedef_check(me.interface.type) ?*/
    return 0;
}

/*# Find the method (if any) that has been marked to be instrumented with
 *# timing points.
 #*/
/*- set timing_method = configuration[me.instance.name].get('%s_timing' % me.interface.name) -*/

/*- for i, m in enumerate(me.interface.type.methods) -*/

/*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/

/*# If we're meant to be timing this method, map its timestamps to the real
 *# measurement functionality. Otherwise, make this a no-op.
 #*/
/*- if timing_method == m.name -*/
    #define _TIMESTAMP(x) TIMESTAMP(x)
/*- else -*/
    #define _TIMESTAMP(x) /* nothing */
/*- endif -*/

/*? marshal.make_marshal_input_symbols(instance, interface, m.name, '%s_marshal_inputs' % m.name, BUFFER_BASE, 'seL4_MsgMaxLength * sizeof(seL4_Word)', i, methods_len, input_parameters, error_handler, threads) ?*/

/*- set name = m.name -*/
/*- set function = '%s_unmarshal_outputs' % m.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set method_index = i -*/
/*- set return_type = m.return_type -*/
/*- set allow_trailing_data = False -*/
/*- include 'unmarshal-outputs.c' -*/

/*- set ret_tls_var = c_symbol('ret_tls_var_from') -*/
/*- if m.return_type is not none -*/
  /*# We will need to take the address of a value representing this return
   *# value at some point. Construct a TLS variable.
   #*/
  /*? make_tls_symbols(macros.show_type(m.return_type), ret_tls_var, threads, False) ?*/
/*- endif -*/

/*- if m.return_type is not none -*/
    /*? macros.show_type(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.interface.name ?*/_/*? m.name ?*/(
/*- for p in m.parameters -*/
  /*- if p.direction == 'in' -*/
    /*- if p.array -*/
      size_t /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char **
      /*- else -*/
        const /*? macros.show_type(p.type) ?*/ *
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      const char *
    /*- else -*/
      /*? macros.show_type(p.type) ?*/
    /*- endif -*/
  /*- else -*/
    /*? assert(p.direction in ['refin', 'out', 'inout']) ?*/
    /*- if p.array -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      size_t * /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char ***
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ **
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      char **
    /*- else -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      /*? macros.show_type(p.type) ?*/ *
    /*- endif -*/
  /*- endif -*/
  /*? p.name ?*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
/*- if len(m.parameters) == 0 -*/
  void
/*- endif -*/
) {
    _TIMESTAMP("glue code entry");

    /*- if not options.frpc_lock_elision or 1 + len(me.instance.type.provides) + len(me.instance.type.consumes) > 1 -*/
        /* We need to surround the send/wait sequence with a lock because this code
         * is potentially concurrent. Without the lock the following sequence can
         * occur:
         *  1. thread A hits send
         *  2. thread B hits send
         *  3. thread B hits wait
         *  4. thread A hits wait
         * As a result, the response intended for thread A is delivered to thread
         * B. Unfortunately we need to take the lock at the start of this function
         * because taking it overwrites our IPC buffer. This locking can be
         * elided in the case when only a single thread will ever be executing
         * inside this function. This is what the conditional above is checking.
         */
        camkes_protect_reply_cap();
        sync_sem_bare_wait(/*? lock_ep ?*/, &/*? lock ?*/);
    /*- endif -*/

    _TIMESTAMP("lock acquired");

    /*- set ret_val = c_symbol('return') -*/
    /*- set ret_ptr = c_symbol('return_ptr') -*/
    /*- if m.return_type is not none -*/
      /*- if m.return_type == 'string' -*/
        char * /*? ret_val ?*/ UNUSED;
        char ** /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- else -*/
        /*? macros.show_type(m.return_type) ?*/ /*? ret_val ?*/ UNUSED;
        /*? macros.show_type(m.return_type) ?*/ * /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- endif -*/
    /*- endif -*/

    /*- set length = c_symbol('length') -*/
    unsigned /*? length ?*/ = /*? marshal.call_marshal_input('%s_marshal_inputs' % m.name, input_parameters) ?*/;
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
        /* Error in marshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if m.return_type == 'string' -*/
                return NULL;
            /*- else -*/
                memset(/*? ret_ptr ?*/, 0, sizeof(* /*? ret_ptr ?*/));
                return * /*? ret_ptr ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    _TIMESTAMP("marshalling done");

    /* Call the endpoint */
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0,
        ROUND_UP_UNSAFE(/*? length ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word));

    seL4_Send(/*? ep ?*/, /*? info ?*/);
    /*- if options.frpc_lock_elision and 1 + len(me.instance.type.provides) + len(me.instance.type.consumes) > 1 -*/
      camkes_protect_reply_cap();
    /*- endif -*/
    /*? info ?*/ = seL4_Recv(/*? ep ?*/, NULL);

    _TIMESTAMP("communication done");

    /*- if not options.frpc_lock_elision or 1 + len(me.instance.type.provides) + len(me.instance.type.consumes) > 1 -*/
        /* It's safe to release the lock here because releasing does not touch our
         * IPC buffer.
         */
        sync_sem_bare_post(/*? lock_ep ?*/, &/*? lock ?*/);
    /*- endif -*/

    _TIMESTAMP("lock released");

    /* Unmarshal the response */
    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/ = seL4_MessageInfo_get_length(/*? info ?*/) * sizeof(seL4_Word);

    /*- set function = '%s_unmarshal_outputs' % m.name -*/
    /*- set return_type = m.return_type -*/
    /*- set err = c_symbol('error') -*/
    int /*? err ?*/ = /*- include 'call-unmarshal-outputs.c' -*/;
    if (unlikely(/*? err ?*/ != 0)) {
        /* Error in unmarshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if m.return_type == 'string' -*/
                return NULL;
            /*- else -*/
                memset(/*? ret_ptr ?*/, 0, sizeof(* /*? ret_ptr ?*/));
                return * /*? ret_ptr ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    _TIMESTAMP("unmarshalling done");

    /*- if m.return_type is not none -*/
        return * /*? ret_ptr ?*/;
    /*- endif -*/
}
#undef _TIMESTAMP
/*- endfor -*/
