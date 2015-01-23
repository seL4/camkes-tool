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
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/marshal.h>
#include <sel4/sel4.h>
#include <camkes/dataport.h>

/*? macros.show_includes(me.to_instance.type.includes) ?*/
/*? macros.show_includes(me.to_interface.type.includes, '../static/components/' + me.to_instance.type.name + '/') ?*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ ((void*)&seL4_GetIPCBuffer()->msg[0])

/*- set methods_len = len(me.from_interface.type.methods) -*/

/*- for m in me.to_interface.type.methods -*/
    extern
    /*- if m.return_type -*/
        /*? show(m.return_type) ?*/
    /*- else -*/
        void
    /*- endif -*/
    /*? me.to_interface.name ?*/_/*? m.name ?*/(
        /*? ', '.join(map(show, m.parameters)) ?*/
    );

/*- set name = m.name -*/
/*- set function = '%s_unmarshal' % m.name -*/
/*- set buffer = BUFFER_BASE -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set input_parameters = filter(lambda('x: x.direction.direction in [\'in\', \'inout\']'), m.parameters) -*/
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
                    /*- set input_parameters = filter(lambda('x: x.direction.direction in [\'in\', \'inout\']'), m.parameters) -*/
                    /*- include 'call-unmarshal-inputs.c' -*/;

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
                                /*- if p.direction.direction in ['inout', 'out'] -*/
                                    &
                                /*- endif -*/
                                /*? p.name ?*/_sz,
                            /*- endif -*/
                            /*- if p.direction.direction in ['inout', 'out'] -*/
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

                    /*# We no longer need anything we previously malloced #*/
                    /*- if m.return_type and (m.return_type.array or (isinstance(m.return_type, camkes.ast.Type) and m.return_type.type == 'string')) -*/
                        free(/*? ret ?*/);
                    /*- endif -*/
                    /*- for p in m.parameters -*/
                        /*- if p.array or (isinstance(p.type, camkes.ast.Type) and p.type.type == 'string') -*/
                            free(/*? p.name ?*/);
                        /*- endif -*/
                    /*- endfor -*/

                    /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /* length */
                        ROUND_UP(/*? length ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word)
                    );

                    /* Send the response */
                    seL4_Send(/*? ep ?*/, /*? info ?*/);

                    break;
                }
            /*- endfor -*/
            default: {
                /*# TODO: Handle error #*/
                assert(0);
            }
        }
    }

    assert(!"Unreachable");
}
