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
/*- from 'helpers/tls.c' import make_tls_symbols -*/

#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/error.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <camkes/dataport.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.interface.type.methods) -*/
/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/
/*- set threads = list(six.moves.range(1, 2 + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes))) -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set allow_trailing_data = False -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*? error.make_error_handler(interface, error_handler) ?*/

/*- for m in me.interface.type.methods -*/
    extern
    /*- if m.return_type is not none-*/
        /*- if m.return_type == 'string' -*/
            char *
        /*- else -*/
            /*? macros.show_type(m.return_type) ?*/
        /*- endif -*/
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
        /*? p.name ?*/
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
        /*? p.name ?*/
      /*- endif -*/
      /*- if not loop.last -*/
        ,
      /*- endif -*/
    /*- endfor -*/
    /*- if len(m.parameters) == 0 -*/
      void
    /*- endif -*/
    );

/*- set name = m.name -*/
/*- set function = '%s_unmarshal_inputs' % m.name -*/
/*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
/*- include 'unmarshal-inputs.c' -*/

/*- set function = '%s_marshal_outputs' % m.name -*/
/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
/*- set return_type = m.return_type -*/
/*- include 'marshal-outputs.c' -*/

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

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

/*- set call_tls_var = c_symbol('call_tls_var_to') -*/
/*- if methods_len <= 1 -*/
  /*- set type = 'unsigned int' -*/
/*- elif methods_len <= 2 ** 8 -*/
  /*- set type = 'uint8_t' -*/
/*- elif methods_len <= 2 ** 16 -*/
  /*- set type = 'uint16_t' -*/
/*- elif methods_len <= 2 ** 32 -*/
  /*- set type = 'uint32_t' -*/
/*- elif methods_len <= 2 ** 64 -*/
  /*- set type = 'uint64_t' -*/
/*- else -*/
  /*? raise(TemplateError('too many methods in interface %s' % me.interface.name)) ?*/
/*- endif -*/
/*? make_tls_symbols(type, call_tls_var, threads, False) ?*/

/*? array_check.make_array_typedef_check_symbols(me.interface.type) ?*/

int /*? me.interface.name ?*/__run(void) {
    /*# Check any typedefs we have been given are not arrays. #*/
    /*? array_check.perform_array_typedef_check(me.interface.type) ?*/

    while (1) {
        /*- set info = c_symbol('info') -*/
        seL4_MessageInfo_t /*? info ?*/ = seL4_Recv(/*? ep ?*/, NULL);

        /*- set size = c_symbol('size') -*/
        unsigned /*? size ?*/ = seL4_MessageInfo_get_length(/*? info ?*/) * sizeof(seL4_Word);
        assert(/*? size ?*/ <= seL4_MsgMaxLength * sizeof(seL4_Word));

        /*- set buffer = c_symbol('buffer') -*/
        void * /*? buffer ?*/ UNUSED = /*? BUFFER_BASE ?*/;

        /*- set call = c_symbol('call') -*/
        /*- set call_ptr = c_symbol('call_ptr') -*/
        /*- if methods_len <= 1 -*/
          unsigned /*? call ?*/ UNUSED;
          unsigned * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
          * /*? call_ptr ?*/ = 0;
        /*- elif methods_len <= 2 ** 8 -*/
          uint8_t /*? call ?*/ UNUSED;
          uint8_t * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
        /*- elif methods_len <= 2 ** 16 -*/
          uint16_t /*? call ?*/ UNUSED;
          uint16_t * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
        /*- elif methods_len <= 2 ** 32 -*/
          uint32_t /*? call ?*/ UNUSED;
          uint32_t * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
        /*- elif methods_len <= 2 ** 64 -*/
          uint64_t /*? call ?*/ UNUSED;
          uint64_t * /*? call_ptr ?*/ = TLS_PTR(/*? call_tls_var ?*/, /*? call ?*/);
        /*- else -*/
          /*? raise(TemplateError('too many methods in interface %s' % me.interface.name)) ?*/
        /*- endif -*/
        /*- if methods_len > 1 -*/
          ERR_IF(sizeof(* /*? call_ptr ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_MALFORMED_RPC_PAYLOAD,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "truncated message encountered while unmarshalling method index in /*? call_tls_var ?*/",
                .length = /*? size ?*/,
                .current_index = sizeof(* /*? call_ptr ?*/),
              }), ({
                  continue;
              }));
          memcpy(/*? call_ptr ?*/, /*? buffer ?*/, sizeof(* /*? call_ptr ?*/));
        /*- endif -*/

        switch (* /*? call_ptr ?*/) {
            /*- for i, m in enumerate(me.interface.type.methods) -*/
                case /*? i ?*/: { /*? '%s%s%s%s%s' % ('/', '* ', m.name, ' *', '/') ?*/
                    /*- for p in m.parameters -*/
                        /*# Declare parameters. #*/
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
                    /*- set function = '%s_unmarshal_inputs' % m.name -*/
                    /*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
                    /*- set err = c_symbol('error') -*/
                    int /*? err ?*/ = /*- include 'call-unmarshal-inputs.c' -*/;
                    if (unlikely(/*? err ?*/ != 0)) {
                        /* Error in unmarshalling; return to event loop. */
                        continue;
                    }

                    /* Call the implementation */
                    /*- set ret = c_symbol('ret') -*/
                    /*- set ret_sz = c_symbol('ret_sz') -*/
                    /*- set ret_ptr = c_symbol('ret_ptr') -*/
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
                            /*- if p.direction == 'in' -*/
                                *
                            /*- endif -*/
                            /*? p.name ?*/_ptr
                            /*- if not loop.last -*/,/*- endif -*/
                        /*- endfor -*/
                    );

                    /* Marshal the response */
                    /*- set function = '%s_marshal_outputs' % m.name -*/
                    /*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
                    /*- set return_type = m.return_type -*/
                    /*- set length = c_symbol('length') -*/
                    unsigned /*? length ?*/ = /*- include 'call-marshal-outputs.c' -*/;

                    /*# We no longer need anything we previously malloced #*/
                    /*- if m.return_type is not none -*/
                      /*- if m.return_type == 'string' -*/
                        free(* /*? ret_ptr ?*/);
                      /*- endif -*/
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
                        /* Error occurred; return to event loop. */
                        continue;
                    }
                    /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /* length */
                        ROUND_UP_UNSAFE(/*? length ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word)
                    );

                    /* Send the response */
                    seL4_Send(/*? ep ?*/, /*? info ?*/);

                    break;
                }
            /*- endfor -*/
            default: {
                ERR(/*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_INVALID_METHOD_INDEX,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "invalid method index received in /*? call_tls_var ?*/",
                        .lower_bound = 0,
                        .upper_bound = /*? methods_len ?*/ - 1,
                        .invalid_index = * /*? call_ptr ?*/,
                    }), ({
                        continue;
                    }));
            }
        }
    }

    UNREACHABLE();
}
