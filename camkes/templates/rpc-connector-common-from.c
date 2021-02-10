/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
/*? marshal.make_marshal_input_symbols(m.name, '%s_marshal_inputs' % m.name, i, methods_len, input_parameters) ?*/

/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
/*? marshal.make_unmarshal_output_symbols(m.name, '%s_unmarshal_outputs' % m.name, i, output_parameters, m.return_type, connector.recv_buffer_size_fixed) ?*/

/*- if m.return_type is not none --*/
    /*? macros.show_type(m.return_type) ?*/ /*- else -*/
    void /*- endif -*/
/*?- me.interface.name ?*/_/*? m.name ?*/(/*? marshal.show_input_parameter_list(m.parameters, ['in', 'refin', 'out', 'inout'], namespace_prefix='p_') ?*/)
{

    /*? begin_send(connector) ?*/

    unsigned size;
    /*-- if m.return_type is not none -*/
      /*? macros.show_type(m.return_type) ?*/ return_val;
      /*? macros.show_type(m.return_type) ?*/ *return_ptr = &return_val;
    /*- endif -*/

    /* Marshal all the parameters */
    unsigned length = /*? marshal.call_marshal_input('%s_marshal_inputs' % m.name, connector.send_buffer, connector.send_buffer_size, input_parameters, namespace_prefix='p_') ?*/;
    if (unlikely(length == UINT_MAX)) {
        /* Error in marshalling; bail out. */
        /*-- if m.return_type is not none -*/
            /*-- if m.return_type == 'string' -*/
                return NULL;
            /*-- else -*/
                memset(return_ptr, 0, sizeof(* return_ptr));
                return * return_ptr;
            /*- endif -*/
        /*-- else -*/
            return;
        /*-- endif -*/
    }

    /*? perform_call(connector, "size", "length", namespace_prefix='rpc_') ?*/

    /* Unmarshal the response */
    int err = /*? marshal.call_unmarshal_output('%s_unmarshal_outputs' % m.name, connector.recv_buffer, "size", output_parameters, m.return_type, "return_ptr", namespace_prefix='p_') ?*/;
    if (unlikely(err != 0)) {
        /* Error in unmarshalling; bail out. */
        /*-- if m.return_type is not none -*/
            /*-- if m.return_type == 'string' -*/
                return NULL;
            /*-- else -*/
                memset(return_ptr, 0, sizeof(* return_ptr));
                return * return_ptr;
            /*-- endif -*/
        /*-- else -*/
            return;
        /*-- endif -*/
    }

    /*? release_recv(connector) ?*/

    /*- if m.return_type is not none -*/
        return *return_ptr;
    /*- endif -*/
}
/*- endfor -*/
