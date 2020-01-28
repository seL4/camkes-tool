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
/*- import 'helpers/marshal.c' as marshal with context -*/

/*? assert(isinstance(connector, namespace)) ?*/

#include <sel4/sel4.h>
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sync/sem-bare.h>
#include <camkes/dataport.h>
#include <camkes/error.h>
#include <camkes/marshal_macros.h>
#include <camkes/tls.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- set methods_len = len(me.interface.type.methods) -*/
/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*? error.make_error_handler(interface, error_handler) ?*/

#define CAMKES_INTERFACE_NAME "/*? interface ?*/"
#define CAMKES_INSTANCE_NAME "/*? instance ?*/"
#define CAMKES_ERROR_HANDLER /*? error_handler ?*/

/*- for i, m in enumerate(me.interface.type.methods) -*/

/*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
/*? marshal.make_marshal_input_symbols(instance, interface, m.name, '%s_marshal_inputs' % m.name, connector.send_buffer, connector.send_buffer_size, i, methods_len, input_parameters, error_handler) ?*/

/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
/*? marshal.make_unmarshal_output_symbols(instance, interface, m.name, '%s_unmarshal_outputs' % m.name, connector.recv_buffer, i, output_parameters, m.return_type, error_handler, connector.recv_buffer_size_fixed) ?*/

/*- if m.return_type is not none -*/
    /*? macros.show_type(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.interface.name ?*/_/*? m.name ?*/(
/*? marshal.show_input_parameter_list(m.parameters, ['in', 'refin', 'out', 'inout']) ?*/
) {

    /*? begin_send(connector) ?*/

    /*- set ret_val = c_symbol('return') -*/
    /*- set ret_ptr = c_symbol('return_ptr') -*/
    /*- if m.return_type is not none -*/
      /*? macros.show_type(m.return_type) ?*/ /*? ret_val ?*/;
      /*? macros.show_type(m.return_type) ?*/ * /*? ret_ptr ?*/ = &/*? ret_val ?*/;
    /*- endif -*/

    /* Marshal all the parameters */
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

    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/;
    /*? perform_call(connector, size, length) ?*/

    /* Unmarshal the response */
    /*- set err = c_symbol('error') -*/
    int /*? err ?*/ = /*? marshal.call_unmarshal_output('%s_unmarshal_outputs' % m.name, size, output_parameters, m.return_type, ret_ptr) ?*/;
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

    /*? release_recv(connector) ?*/

    /*- if m.return_type is not none -*/
        return * /*? ret_ptr ?*/;
    /*- endif -*/
}
/*- endfor -*/
