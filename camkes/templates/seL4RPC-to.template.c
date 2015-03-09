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
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/marshal.h>
#include <camkes/error.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <camkes/dataport.h>
#include <utils/util.h>

/*? macros.show_includes(me.to_instance.type.includes) ?*/
/*? macros.show_includes(me.to_interface.type.includes, '../static/components/' + me.to_instance.type.name + '/') ?*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.to_interface.type.methods) -*/
/*- set instance = me.to_instance.name -*/
/*- set interface = me.to_interface.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set allow_trailing_data = False -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.to_interface.name -*/
/*- include 'error-handler.c' -*/

/*- for m in me.to_interface.type.methods -*/
    extern
    /*- if m.return_type -*/
        /*? show(m.return_type) ?*/
    /*- else -*/
        void
    /*- endif -*/
    /*? me.to_interface.name ?*/_/*? m.name ?*/(
    /*- for p in m.parameters -*/
      /*- if p.direction.direction == 'in' -*/
        /*- if p.array -*/
          size_t /*? p.name ?*/_sz,
          /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
            char **
          /*- else -*/
            /*? show(p.type) ?*/ *
          /*- endif -*/
        /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          char *
        /*- else -*/
          /*? show(p.type) ?*/
        /*- endif -*/
        /*? p.name ?*/
      /*- else -*/
        /*? assert(p.direction.direction in ['refin', 'out', 'inout']) ?*/
        /*- if p.array -*/
          size_t * /*? p.name ?*/_sz,
          /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
            char ***
          /*- else -*/
            /*? show(p.type) ?*/ **
          /*- endif -*/
        /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
          char **
        /*- else -*/
          /*? show(p.type) ?*/ *
        /*- endif -*/
        /*? p.name ?*/
      /*- endif -*/
      /*- if not loop.last -*/
        ,
      /*- endif -*/
    /*- endfor -*/
    );

/*- set name = m.name -*/
/*- set function = '%s_unmarshal' % m.name -*/
/*- set input_parameters = filter(lambda('x: x.direction.direction in [\'refin\', \'in\', \'inout\']'), m.parameters) -*/
/*- include 'unmarshal-inputs.c' -*/

/*- set function = '%s_marshal' % m.name -*/
/*- set output_parameters = filter(lambda('x: x.direction.direction in [\'out\', \'inout\']'), m.parameters) -*/
/*- set return_type = m.return_type -*/
/*- include 'marshal-outputs.c' -*/

/*- endfor -*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

int /*? me.to_interface.name ?*/__run(void) {
    while (1) {
        /*- set info = c_symbol('info') -*/
        seL4_MessageInfo_t /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);

        /*- set size = c_symbol('size') -*/
        unsigned int /*? size ?*/ = seL4_MessageInfo_get_length(/*? info ?*/) * sizeof(seL4_Word);
        assert(/*? size ?*/ <= seL4_MsgMaxLength * sizeof(seL4_Word));

        /*- set buffer = c_symbol('buffer') -*/
        void * /*? buffer ?*/ UNUSED = /*? BUFFER_BASE ?*/;

        /*- set call = c_symbol('call') -*/
        /*- if methods_len <= 1 -*/
          unsigned int /*? call ?*/ = 0;
        /*- else -*/
          /*- if methods_len <= 2 ** 8 -*/
            uint8_t
          /*- elif methods_len <= 2 ** 16 -*/
            uint16_t
          /*- elif methods_len <= 2 ** 32 -*/
            uint32_t
          /*- elif methods_len <= 2 ** 64 -*/
            uint64_t
          /*- else -*/
            /*? raise(Exception('too many methods in interface %s' % me.to_interface.name)) ?*/
          /*- endif -*/
          /*? call ?*/;
          ERR_IF(sizeof(/*? call ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_MALFORMED_RPC_PAYLOAD,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "truncated message encountered while unmarshalling method index in /*? name ?*/",
                .length = /*? size ?*/,
                .current_index = sizeof(/*? call ?*/),
              }), ({
                  continue;
              }));
          memcpy(& /*? call ?*/, /*? buffer ?*/, sizeof(/*? call ?*/));
        /*- endif -*/

        switch (/*? call ?*/) {
            /*- for i, m in enumerate(me.to_interface.type.methods) -*/
                case /*? i ?*/: { /*? '/' + '* ' + m.name + ' *' + '/' ?*/
                    /*- for p in m.parameters -*/
                        /*# Declare parameters. #*/
                        /*- if p.array -*/
                            size_t /*? p.name ?*/_sz;
                            /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                                char ** /*? p.name ?*/ = NULL;
                            /*- else -*/
                                /*? show(p.type) ?*/ * /*? p.name ?*/ = NULL;
                            /*- endif -*/
                        /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                            char * /*? p.name ?*/ = NULL;
                        /*- else -*/
                            /*? show(p.type) ?*/ /*? p.name ?*/;
                        /*- endif -*/
                    /*- endfor -*/

                    /* Unmarshal parameters */
                    /*- set function = '%s_unmarshal' % m.name -*/
                    /*- set input_parameters = filter(lambda('x: x.direction.direction in [\'refin\', \'in\', \'inout\']'), m.parameters) -*/
                    /*- set err = c_symbol('error') -*/
                    int /*? err ?*/ = /*- include 'call-unmarshal-inputs.c' -*/;
                    if (unlikely(/*? err ?*/ != 0)) {
                        /* Error in unmarshalling; return to event loop. */
                        continue;
                    }

                    /* Call the implementation */
                    /*- set ret = c_symbol('ret') -*/
                    /*- set ret_sz = c_symbol('ret_sz') -*/
                    /*- if m.return_type -*/
                        /*- if m.return_type.array -*/
                            size_t /*? ret_sz ?*/;
                            /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                                char **
                            /*- else -*/
                                /*? show(m.return_type) ?*/ *
                            /*- endif -*/
                        /*- elif isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                            char *
                        /*- else -*/
                            /*? show(m.return_type) ?*/
                        /*- endif -*/
                        /*? ret ?*/ =
                    /*- endif -*/
                    /*? me.to_interface.name ?*/_/*? m.name ?*/(
                        /*- if m.return_type and m.return_type.array -*/
                            & /*? ret_sz ?*/
                            /*- if len(m.parameters) > 0 -*/
                                ,
                            /*- endif -*/
                        /*- endif -*/
                        /*- for p in m.parameters -*/
                            /*- if p.array -*/
                                /*- if p.direction.direction in ['refin', 'inout', 'out'] -*/
                                    &
                                /*- endif -*/
                                /*? p.name ?*/_sz,
                            /*- endif -*/
                            /*- if p.direction.direction in ['refin', 'inout', 'out'] -*/
                                &
                            /*- endif -*/
                            /*? p.name ?*/
                            /*- if not loop.last -*/,/*- endif -*/
                        /*- endfor -*/
                    );

                    /* Marshal the response */
                    /*- set function = '%s_marshal' % m.name -*/
                    /*- set output_parameters = filter(lambda('x: x.direction.direction in [\'out\', \'inout\']'), m.parameters) -*/
                    /*- set return_type = m.return_type -*/
                    /*- set length = c_symbol('length') -*/
                    unsigned int /*? length ?*/ = /*- include 'call-marshal-outputs.c' -*/;
                    if (unlikely(/*? length ?*/ == UINT_MAX)) {
                        /* Error occurred in unmarshalling; return to event loop. */
                        continue;
                    }

                    /*# We no longer need anything we previously malloced #*/
                    /*- if m.return_type -*/
                      /*- if m.return_type.array -*/
                        /*- if isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                          /*- set mcount = c_symbol() -*/
                          for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? ret_sz ?*/; /*? mcount ?*/ ++) {
                            free(/*? ret ?*/[/*? mcount ?*/]);
                          }
                        /*- endif -*/
                        free(/*? ret ?*/);
                      /*- elif isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string' -*/
                        free(/*? ret ?*/);
                      /*- endif -*/
                    /*- endif -*/
                    /*- for p in m.parameters -*/
                      /*- if p.array -*/
                        /*- if isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                          /*- set mcount = c_symbol() -*/
                          for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
                            free(/*? p.name ?*/[/*? mcount ?*/]);
                          }
                        /*- endif -*/
                        free(/*? p.name ?*/);
                      /*- elif isinstance(p.type, camkes.ast.Type) and p.type.type == 'string' -*/
                        free(/*? p.name ?*/);
                      /*- endif -*/
                    /*- endfor -*/

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
                        .description = "invalid method index received in /*? name ?*/",
                        .lower_bound = 0,
                        .upper_bound = /*? methods_len ?*/ - 1,
                        .invalid_index = /*? call ?*/,
                    }), ({
                        continue;
                    }));
            }
        }
    }

    UNREACHABLE();
}
