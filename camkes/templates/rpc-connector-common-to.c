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

/*? assert(isinstance(connector, namespace)) ?*/

#include <autoconf.h>
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/error.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <camkes/dataport.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/
/*# Count how many threads are in this component. This is because we want to create some
  # thread local variables, but we don't have a way to map our general thread ID to an
  # index into threads that specifically are spawned for this connector. I.e. a component
  # may have 8 threads in total, and 2 threads running this connector, but without knowing
  # what IDs those 2 threads will have we simply assume it might be any of the 8 #*/
/*- set threads = list(six.moves.range(1, 2 + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes))) -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*? error.make_error_handler(interface, error_handler) ?*/

/*# Construct a dict from interface types to list of from ends indecies #*/
/*- set type_dict = {} -*/
/*- for f in me.parent.from_ends -*/
    /*- set cur_list = type_dict.get(f.interface.type, []) -*/
    /*- do cur_list.append(loop.index0) -*/
    /*- do type_dict.update({f.interface.type: cur_list}) -*/
/*- endfor -*/

/*- set methods_list = [] -*/
/*- set call_tls_var_list = [] -*/

/*- for f in me.parent.from_ends -*/
    /*- set methods_len = len(f.interface.type.methods) -*/
    /*- do methods_list.append(methods_len) -*/
    /*- for m in f.interface.type.methods -*/
        extern
        /*- if m.return_type is not none -*/
            /*? macros.show_type(m.return_type) ?*/
        /*- else -*/
            void
        /*- endif -*/
            /*? me.interface.name ?*/_/*? m.name ?*/(
                /*? marshal.show_input_parameter_list(m.parameters, ['in', 'refin', 'out', 'inout']) ?*/
                /*- if len(m.parameters) == 0 -*/
                    void
                /*- endif -*/
            );

        /*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
        /*? marshal.make_unmarshal_input_symbols(instance, interface, m.name, '%s_unmarshal_inputs' % m.name, connector.recv_buffer, methods_len, input_parameters, error_handler, connector.recv_buffer_size_fixed) ?*/

        /*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
        /*? marshal.make_marshal_output_symbols(instance, interface, m.name, '%s_marshal_outputs' % m.name, connector.send_buffer, connector.send_buffer_size, output_parameters, m.return_type, error_handler) ?*/

        /*- if m.return_type is not none -*/
            /*? make_tls_symbols(macros.show_type(m.return_type), '%s_ret_to' % m.name, threads, False) ?*/
        /*- endif -*/
        /*- for p in m.parameters -*/
            /*- if p.array -*/
                /*? make_tls_symbols('size_t', '%s_%s_sz_to' % (m.name, p.name), threads, False) ?*/
                /*? make_tls_symbols('%s*' % macros.show_type(p.type), '%s_%s_to' % (m.name, p.name), threads, False) ?*/
            /*- else -*/
                /*? make_tls_symbols(macros.show_type(p.type), '%s_%s_to' % (m.name, p.name), threads, False) ?*/
            /*- endif -*/
        /*- endfor -*/

    /*- endfor -*/
    /*- set call_tls_var = c_symbol('call_tls_var_to') -*/
    /*- set type = macros.type_to_fit_integer(methods_len) -*/
    /*? make_tls_symbols(type, call_tls_var, threads, False) ?*/
    /*- do call_tls_var_list.append(call_tls_var) -*/
/*- endfor -*/


/*? array_check.make_array_typedef_check_symbols(me.interface.type) ?*/

/*- set p = Perspective(instance=me.instance.name, interface=me.interface.name) -*/
/*- set passive = options.realtime and configuration[me.instance.name].get(p['passive_attribute'], False) -*/

/*# Passive interface "run" functions must be passed a ntfn cap as part of the passive thread init protocol.
 *# As such if this is a passive interface, a different function prototype is needed for "run".
 #*/
int
/*- if passive -*/
    /*- set init_ntfn = c_symbol() -*/
    /*? me.interface.name ?*/__run_passive(seL4_CPtr /*? init_ntfn ?*/)
/*- else -*/
    /*? me.interface.name ?*/__run(void)
/*- endif -*/
{

    /*# Check any typedefs we have been given are not arrays. #*/
    /*? array_check.perform_array_typedef_check(me.interface.type) ?*/

    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/ UNUSED;
    /*- if passive -*/
        /*? recv_first_rpc(connector, size, me.might_block(), notify_cptr = init_ntfn) ?*/
    /*- else -*/
        /*? recv_first_rpc(connector, size, me.might_block()) ?*/
    /*- endif -*/

    while (1) {
        /*- if len(type_dict.keys()) > 1 -*/
            switch (/*? connector.badge_symbol ?*/) {
        /*- endif -*/
        /*- for from_type in type_dict.keys() -*/
            /*- set methods_len = methods_list[type_dict.get(from_type)[0]] -*/
            /*- set call_tls_var = call_tls_var_list[type_dict.get(from_type)[0]] -*/
            /*- if len(type_dict.keys()) > 1 -*/
                /*- for from_index in type_dict.get(from_type) -*/
                    case /*? connector.badges[from_index] ?*/: {
                /*- endfor -*/
            /*- endif -*/

            /*- set call = c_symbol('call') -*/
            /*- set call_ptr = c_symbol('call_ptr') -*/
            /*- if methods_len <= 1 -*/
                unsigned /*? call ?*/ UNUSED;
                unsigned * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
                * /*? call_ptr ?*/ = 0;
            /*- else -*/
                /*- set type = macros.type_to_fit_integer(methods_len) -*/
                /*? type ?*/ /*? call ?*/ UNUSED;
                /*? type ?*/ * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
            /*- endif -*/
            /*- if methods_len > 1 -*/
                ERR_IF(sizeof(* /*? call_ptr ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling method index in /*? me.interface.name ?*/",
                    .length = /*? size ?*/,
                    .current_index = sizeof(* /*? call_ptr ?*/),
                    }), ({
                        /*? complete_recv(connector) ?*/
                        /*? begin_recv(connector, size, me.might_block()) ?*/
                        continue;
                }));

                memcpy(/*? call_ptr ?*/, /*? connector.recv_buffer ?*/, sizeof(* /*? call_ptr ?*/));
            /*- endif -*/

            switch (* /*? call_ptr ?*/) {
                /*- for i, m in enumerate(from_type.methods) -*/
                    case /*? i ?*/: { /*? '%s%s%s%s%s' % ('/', '* ', m.name, ' *', '/') ?*/
                        /*# Declare parameters. #*/
                        /*- for p in m.parameters -*/

                            /*- if p.array -*/
                                size_t /*? p.name ?*/_sz UNUSED;
                                size_t * /*? p.name ?*/_sz_ptr = TLS_PTR(/*? m.name ?*/_/*? p.name ?*/_sz_to, /*? p.name ?*/_sz);
                                /*- if p.type == 'string' -*/
                                    char ** /*? p.name ?*/ UNUSED = NULL;
                                    char *** /*? p.name ?*/_ptr = TLS_PTR(/*? m.name ?*/_/*? p.name ?*/_to, /*? p.name ?*/);
                                /*- else -*/
                                    /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/ UNUSED = NULL;
                                    /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/_ptr = TLS_PTR(/*? m.name ?*/_/*? p.name ?*/_to, /*? p.name ?*/);
                                /*- endif -*/
                            /*- elif p.type == 'string' -*/
                                char * /*? p.name ?*/ UNUSED = NULL;
                                char ** /*? p.name ?*/_ptr = TLS_PTR(/*? m.name ?*/_/*? p.name ?*/_to, /*? p.name ?*/);
                            /*- else -*/
                                /*? macros.show_type(p.type) ?*/ /*? p.name ?*/ UNUSED;
                                /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/_ptr = TLS_PTR(/*? m.name ?*/_/*? p.name ?*/_to, /*? p.name ?*/);
                            /*- endif -*/
                        /*- endfor -*/

                        /* Unmarshal parameters */
                        /*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
                        /*- set err = c_symbol('error') -*/
                        int /*? err ?*/ = /*? marshal.call_unmarshal_input('%s_unmarshal_inputs' % m.name, size, input_parameters) ?*/;
                        if (unlikely(/*? err ?*/ != 0)) {
                            /* Error in unmarshalling; return to event loop. */
                            /*? complete_recv(connector) ?*/
                            /*? begin_recv(connector, size, me.might_block()) ?*/
                            continue;
                        }

                        /* Call the implementation */
                        /*- set ret = c_symbol('ret') -*/
                        /*- set ret_sz = c_symbol('ret_sz') -*/
                        /*- set ret_ptr = c_symbol('ret_ptr') -*/
                        /*- set ret_sz_ptr = c_symbol('ret_sz_ptr') -*/
                        /*- if m.return_type is not none -*/
                            /*- if m.return_type == 'string' -*/
                                char * /*? ret ?*/ UNUSED;
                                char ** /*? ret_ptr ?*/ = TLS_PTR(/*? m.name ?*/_ret_to, /*? ret ?*/);
                            /*- else -*/
                                /*? macros.show_type(m.return_type) ?*/ /*? ret ?*/ UNUSED;
                                /*? macros.show_type(m.return_type) ?*/ * /*? ret_ptr ?*/ = TLS_PTR(/*? m.name ?*/_ret_to, /*? ret ?*/);
                            /*- endif -*/
                            * /*? ret_ptr ?*/ =
                        /*- endif -*/
                        /*? me.interface.name ?*/_/*? m.name ?*/(
                            /*- for p in m.parameters -*/
                                /*- if p.array -*/
                                    /*- if p.direction == 'in' -*/
                                        *
                                    /*- endif -*/
                                    /*? p.name ?*/_sz_ptr,
                                /*- endif -*/
                                /*- if p.direction =='in' -*/
                                    *
                                /*- endif -*/
                                /*? p.name ?*/_ptr
                                /*- if not loop.last -*/,/*- endif -*/
                            /*- endfor -*/
                        );

                        /*? complete_recv(connector) ?*/
                        /*? begin_reply(connector) ?*/

                        /* Marshal the response */
                        /*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
                        /*- set length = c_symbol('length') -*/
                        unsigned /*? length ?*/ = /*? marshal.call_marshal_output('%s_marshal_outputs' % m.name, output_parameters, m.return_type, ret_ptr) ?*/;

                        /*# We no longer need anything we previously malloced #*/
                        /*- if m.return_type == 'string' -*/
                            free(* /*? ret_ptr ?*/);
                        /*- endif -*/
                        /*- for p in m.parameters -*/
                            /*- if p.array -*/
                                /*- if p.type == 'string' -*/
                                    /*- set mcount = c_symbol() -*/
                                    for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz_ptr; /*? mcount ?*/ ++) {
                                        free((* /*? p.name ?*/_ptr)[/*? mcount ?*/]);
                                    }
                                /*- endif -*/
                                free(* /*? p.name ?*/_ptr);
                            /*- elif p.type == 'string' -*/
                                free(* /*? p.name ?*/_ptr);
                            /*- endif -*/
                        /*- endfor -*/

                        /* Check if there was an error during marshalling. We do
                         * this after freeing internal parameter variables to avoid
                         * leaking memory on errors.
                         */
                        if (unlikely(/*? length ?*/ == UINT_MAX)) {
                            /*? complete_reply(connector) ?*/
                            /*? begin_recv(connector, size, me.might_block()) ?*/
                            continue;
                        }

                        /*? reply_recv(connector, length, size, me.might_block()) ?*/

                        break;
                    }
                /*- endfor -*/
                default: {
                    ERR(/*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_INVALID_METHOD_INDEX,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "invalid method index received in /*? me.interface.name ?*/",
                        .lower_bound = 0,
                        .upper_bound = /*? methods_len ?*/ - 1,
                        .invalid_index = * /*? call_ptr ?*/,
                    }), ({
                        /*? complete_recv(connector) ?*/
                        /*? begin_recv(connector, size, me.might_block()) ?*/
                        continue;
                    }));
                }
            }
            /*- if len(type_dict.keys()) > 1 -*/
                break;
            }
            /*- endif -*/
        /*- endfor -*/
        /*- if len(type_dict.keys()) > 1 -*/
            default:
                ERR(/*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "unknown badge while unmarshalling method in /*? me.interface.name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? connector.badge_symbol ?*/,
                    }), ({
                        /*? complete_recv(connector) ?*/
                        /*? begin_recv(connector, size, me.might_block()) ?*/
                        continue;
                    }));
                break;
        }
        /*- endif -*/
    }

    UNREACHABLE();
}
