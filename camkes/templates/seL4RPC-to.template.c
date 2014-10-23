/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

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
/*- endfor -*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

int /*? me.to_interface.name ?*/__run(void) {
    while (1) {
        /*- set info = c_symbol('info') -*/
        seL4_MessageInfo_t /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);

        /*- set buffer = c_symbol('buffer') -*/
        void * /*? buffer ?*/ = /*? BUFFER_BASE ?*/;

        /* We should have at least been passed a method index */
        assert(seL4_MessageInfo_get_length(/*? info ?*/) >= 1);
        /*- set call = c_symbol('call') -*/
        int /*? call ?*/;
        /*? macros.unmarshal(buffer, call, 'sizeof(int)') ?*/

        switch (/*? call ?*/) {
            /*- for i, m in enumerate(me.to_interface.type.methods) -*/
                case /*? i ?*/: { /*? '/' + '* ' + m.name + ' *' + '/' ?*/
                    /* Unmarshal parameters */
                    /*- for p in m.parameters -*/

                        /*# Declare parameters. #*/
                        /*- if p.array -*/
                            size_t /*? p.name ?*/_sz = 0;
                        /*- endif -*/
                        /*? show(p.type) ?*/ /*- if p.array -*/ * /*- endif -*/ /*? p.name ?*/
                            /*- if p.array -*/
                                = NULL
                            /*- endif -*/
                            ;

                        /*- if p.direction.direction in ['inout', 'in'] -*/
                            /*- if p.array -*/
                                /*? macros.unmarshal_array(buffer, p.name, 'sizeof(%s)' % show(p.type), False, show(p.type)) ?*/
                            /*- else -*/
                                /*- if p.type.type == 'string' -*/
                                    /*? macros.unmarshal_string(buffer, p.name, True) ?*/
                                /*- else -*/
                                    /*? macros.unmarshal(buffer, p.name, 'sizeof(%s)' % show(p.type)) ?*/
                                /*- endif -*/
                            /*- endif -*/
                        /*- endif -*/
                    /*- endfor -*/

                    /* Call the implementation */
                    /*- if m.return_type -*/
                        /*- set ret = c_symbol('ret') -*/
                        /*? show(m.return_type) ?*/ /*? ret ?*/ =
                    /*- endif -*/
                    /*? me.to_interface.name ?*/_/*? m.name ?*/(
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
                    /*? buffer ?*/ = /*? BUFFER_BASE ?*/;
                    /*- if m.return_type -*/
                        /*- if m.return_type.type == 'string' -*/
                            /*? macros.marshal_string(buffer, ret) ?*/
                        /*- else -*/
                            /*? macros.marshal(buffer, ret, 'sizeof(%s)' % show(m.return_type)) ?*/
                        /*- endif -*/
                    /*- endif -*/
                    /*- for p in m.parameters -*/
                        /*- if p.direction.direction in ['inout', 'out'] -*/
                            /*- if p.array -*/
                                /*? macros.marshal_array(buffer, p.name, 'sizeof(%s)' % show(p.type)) ?*/
                            /*- elif p.type.type == 'string' -*/
                                /*? macros.marshal_string(buffer, p.name) ?*/
                            /*- else -*/
                                /*? macros.marshal(buffer, p.name, 'sizeof(%s)' % show(p.type)) ?*/
                            /*- endif -*/
                        /*- endif -*/
                    /*- endfor -*/
                    /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /* length */
                        ROUND_UP(/*? buffer ?*/ - /*? BUFFER_BASE ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word)
                    );

                    /* Send the response */
                    seL4_Send(/*? ep ?*/, /*? info ?*/);

                    /* Free any malloced variables */
                    /*- for p in m.parameters -*/
                        /*- if p.array or p.type.type == 'string' -*/
                            free(/*? p.name ?*/);
                        /*- endif -*/
                    /*- endfor -*/

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
