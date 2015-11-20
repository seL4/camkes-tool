/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <sel4/sel4.h>
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/marshal.h>
#include <camkes/dataport.h>
#include <camkes/error.h>
#include <camkes/timing.h>
#include <camkes/tls.h>
#include <sync/sem-bare.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/
/*? macros.show_includes(me.from_interface.type.includes, '../static/components/' + me.from_instance.type.name + '/') ?*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.from_interface.type.methods) -*/
/*- set instance = me.from_instance.name -*/
/*- set interface = me.from_interface.name -*/
/*- set threads = list(range(1, 2 + len(me.from_instance.type.provides) + len(me.from_instance.type.uses) + len(me.from_instance.type.emits) + len(me.from_instance.type.consumes))) -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.from_interface.name -*/
/*- include 'error-handler.c' -*/

/*- if not options.frpc_lock_elision or len([me.from_instance.type.control] + me.from_instance.type.provides + me.from_instance.type.consumes) > 1 -*/
    /*# See below for an explanation of this conditional. #*/
    /*- set lock_ep = alloc('lock', seL4_EndpointObject, read=True, write=True) -*/
    /*- set lock = c_symbol('lock') -*/
    static volatile int /*? lock ?*/ = 1;
/*- endif -*/

TIMING_DEFS(/*? me.from_interface.name ?*/, "glue code entry", "lock acquired", "marshalling done", "communication done", "lock released", "unmarshalling done")

/*- include 'array-typedef-check.c' -*/

int /*? me.from_interface.name ?*/__run(void) {
    /*# Check any typedefs we have been given are not arrays. #*/
    /*- include 'call-array-typedef-check.c' -*/
    return 0;
}

/*# Find the method (if any) that has been marked to be instrumented with
 *# timing points.
 #*/
/*- set timing_method = configuration[me.from_instance.name].get('%s_timing' % me.from_interface.name) -*/

/*- for i, m in enumerate(me.from_interface.type.methods) -*/

/*- set input_parameters = filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters) -*/
/*- set output_parameters = filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters) -*/

/*# If we're meant to be timing this method, map its timestamps to the real
 *# measurement functionality. Otherwise, make this a no-op.
 #*/
/*- if timing_method == m.name -*/
    #define _TIMESTAMP(x) TIMESTAMP(x)
/*- else -*/
    #define _TIMESTAMP(x) /* nothing */
/*- endif -*/

/*- set name = m.name -*/
/*- set function = '%s_marshal_inputs' % m.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set method_index = i -*/
/*- include 'marshal-inputs.c' -*/

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
  /*- set name = ret_tls_var -*/
  /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
    /*- set array = False -*/
    /*- set type = 'char*' -*/
    /*- include 'thread_local.c' -*/
  /*- else -*/
    /*- set array = False -*/
    /*- set type = show(m.return_type) -*/
    /*- include 'thread_local.c' -*/
  /*- endif -*/
/*- endif -*/

/*- if m.return_type is not none -*/
    /*? show(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/(
/*- for p in m.parameters -*/
  /*- if p.direction == 'in' -*/
    /*- if p.array -*/
      size_t /*? p.name ?*/_sz,
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        char **
      /*- else -*/
        const /*? show(p.type) ?*/ *
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      const char *
    /*- else -*/
      /*? show(p.type) ?*/
    /*- endif -*/
  /*- else -*/
    /*? assert(p.direction in ['refin', 'out', 'inout']) ?*/
    /*- if p.array -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      size_t * /*? p.name ?*/_sz,
      /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
        char ***
      /*- else -*/
        /*? show(p.type) ?*/ **
      /*- endif -*/
    /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
      char **
    /*- else -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      /*? show(p.type) ?*/ *
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

    /*- if not options.frpc_lock_elision or len([me.from_instance.type.control] + me.from_instance.type.provides + me.from_instance.type.consumes) > 1 -*/
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
        sync_sem_bare_wait(/*? lock_ep ?*/, &/*? lock ?*/);
    /*- endif -*/

    _TIMESTAMP("lock acquired");

    /*- set ret_val = c_symbol('return') -*/
    /*- set ret_ptr = c_symbol('return_ptr') -*/
    /*- if m.return_type is not none -*/
      /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
        char * /*? ret_val ?*/ UNUSED;
        char ** /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- else -*/
        /*? show(m.return_type) ?*/ /*? ret_val ?*/ UNUSED;
        /*? show(m.return_type) ?*/ * /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- endif -*/
    /*- endif -*/

    /*- set function = '%s_marshal_inputs' % m.name -*/
    /*- set length = c_symbol('length') -*/
    unsigned int /*? length ?*/ = /*- include 'call-marshal-inputs.c' -*/;
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
        /* Error in marshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
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
    /*? info ?*/ = seL4_Recv(/*? ep ?*/, NULL);

    _TIMESTAMP("communication done");

    /*- if not options.frpc_lock_elision or len([me.from_instance.type.control] + me.from_instance.type.provides + me.from_instance.type.consumes) > 1 -*/
        /* It's safe to release the lock here because releasing does not touch our
         * IPC buffer.
         */
        sync_sem_bare_post(/*? lock_ep ?*/, &/*? lock ?*/);
    /*- endif -*/

    _TIMESTAMP("lock released");

    /* Unmarshal the response */
    /*- set size = c_symbol('size') -*/
    unsigned int /*? size ?*/ = seL4_MessageInfo_get_length(/*? info ?*/) * sizeof(seL4_Word);

    /*- set function = '%s_unmarshal_outputs' % m.name -*/
    /*- set return_type = m.return_type -*/
    /*- set err = c_symbol('error') -*/
    int /*? err ?*/ = /*- include 'call-unmarshal-outputs.c' -*/;
    if (unlikely(/*? err ?*/ != 0)) {
        /* Error in unmarshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
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
