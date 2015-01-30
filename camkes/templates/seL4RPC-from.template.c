/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#define _POSIX_SOURCE /* stpcpy */
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
#include <sync/sem-bare.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/
/*? macros.show_includes(me.from_interface.type.includes, '../static/components/' + me.from_instance.type.name + '/') ?*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.from_interface.type.methods) -*/
/*- set instance = me.from_instance.name -*/
/*- set interface = me.from_interface.name -*/

/* Interface-specific error handling */
/*- set error_handler = c_symbol('error_handler') -*/
/*- include 'error-handler.c' -*/

/*- if not options.frpc_lock_elision or len([me.from_instance.type.control] + me.from_instance.type.provides + me.from_instance.type.consumes) > 1 -*/
    /*# See below for an explanation of this conditional. #*/
    /*- set lock_ep = alloc('lock', seL4_EndpointObject, read=True, write=True) -*/
    /*- set lock = c_symbol('lock') -*/
    static volatile int /*? lock ?*/ = 1;
/*- endif -*/

TIMING_DEFS(/*? me.from_interface.name ?*/, "glue code entry", "lock acquired", "marshalling done", "communication done", "lock released", "unmarshalling done");

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing to be done. */
    return 0;
}

/*# Find the method (if any) that has been marked to be instrumented with
 *# timing points.
 #*/
/*- set timing_method = [] -*/
/*- if configuration -*/
    /*- set timing_setting = filter(lambda('x: x.instance == \'%s\' and x.attribute == \'%s_timing\'' % (me.from_instance.name, me.from_interface.name)), configuration.settings) -*/
    /*- if len(timing_setting) > 0 -*/
        /*- do timing_method.append(timing_setting[0].value) -*/
    /*- endif -*/
/*- endif -*/
/*- set timing_method = timing_method[0] if len(timing_method) > 0 else None -*/

/*- for i, m in enumerate(me.from_interface.type.methods) -*/

/*- set input_parameters = filter(lambda('x: x.direction.direction in [\'in\', \'inout\']'), m.parameters) -*/
/*- set output_parameters = filter(lambda('x: x.direction.direction in [\'out\', \'inout\']'), m.parameters) -*/

/*# If we're meant to be timing this method, map its timestamps to the real
 *# measurement functionality. Otherwise, make this a no-op.
 #*/
/*- if timing_connector == m.name -*/
    #define _TIMESTAMP(x) TIMESTAMP(x)
/*- else -*/
    #define _TIMESTAMP(x) /* nothing */
/*- endif -*/

/*- set name = m.name -*/
/*- set function = '%s_marshal' % m.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set method_index = i -*/
/*- include 'marshal-inputs.c' -*/

/*- set name = m.name -*/
/*- set function = '%s_unmarshal' % m.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set method_index = i -*/
/*- set return_type = m.return_type -*/
/*- set allow_trailing_data = False -*/
/*- include 'unmarshal-outputs.c' -*/

/*- if m.return_type -*/
    /*? show(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/(
/*- set ret_sz = c_symbol('ret_sz') -*/
/*- if m.return_type and m.return_type.array -*/
    size_t * /*? ret_sz ?*/
    /*- if len(m.parameters) > 0 -*/
        ,
    /*- endif -*/
/*- endif -*/
    /*? ', '.join(map(show, m.parameters)) ?*/
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

    /*- set function = '%s_marshal' % m.name -*/
    /*- set length = c_symbol('length') -*/
    unsigned int /*? length ?*/ = /*- include 'call-marshal-inputs.c' -*/;
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
        /* Error in marshalling; bail out. */
        /*- if m.return_type -*/
            /*- if m.return_type.array or (isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string')  -*/
                return NULL;
            /*- else -*/
                /*- set ret = c_symbol() -*/
                /*? show(m.return_type) ?*/ /*? ret ?*/;
                memset(& /*? ret ?*/, 0, sizeof(/*? ret ?*/));
                return /*? ret ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    _TIMESTAMP("marshalling done");

    /* Call the endpoint */
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0,
        ROUND_UP(/*? length ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word));

    seL4_Send(/*? ep ?*/, /*? info ?*/);
    /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);

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

    /*- set function = '%s_unmarshal' % m.name -*/
    /*- set return_type = m.return_type -*/
    /*- set ret = c_symbol('return') -*/
    /*- if return_type -*/
      /*- if return_type.array -*/
        /*- if isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
          char **
        /*- else -*/
          /*? show(return_type) ?*/ *
        /*- endif -*/
      /*- elif isinstance(return_type, camkes.ast.Type) and return_type.type == 'string' -*/
        char *
      /*- else -*/
        /*? show(return_type) ?*/
      /*- endif -*/
      /*? ret ?*/;
    /*- endif -*/
    /*- set err = c_symbol('error') -*/
    int /*? err ?*/ = /*- include 'call-unmarshal-outputs.c' -*/;
    if (unlikely(/*? err ?*/ != 0)) {
        /* Error in unmarshalling; bail out. */
        /*- if m.return_type -*/
            /*- if m.return_type.array or (isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string')  -*/
                return NULL;
            /*- else -*/
                memset(& /*? ret ?*/, 0, sizeof(/*? ret ?*/));
                return /*? ret ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    _TIMESTAMP("unmarshalling done");

    /*- if m.return_type -*/
        return /*? ret ?*/;
    /*- endif -*/
}
#undef _TIMESTAMP
/*- endfor -*/
