/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <assert.h>
#include <camkes/tls.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sel4/sel4.h>
#include <sys/reg.h>
#include <utils/util.h>

/*? macros.show_includes(me.to_instance.type.includes) ?*/
/*? macros.show_includes(me.to_interface.type.includes, '../static/components/' + me.to_instance.type.name + '/') ?*/

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

/*# Necessary TLS variables #*/
/*- set threads = [1] + map(lambda('x: x + 2'), range(len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.emits + me.to_instance.type.consumes + me.to_instance.type.dataports))) -*/
/*- for m in me.to_interface.type.methods -*/
    /*- for p in m.parameters -*/
    /*# XXX: We only need to do this TLS instantiation for 'out' and 'inout' variables, but for simplicity we currently do it for everything. #*/
        /*- set type = show(p.type) -*/
        /*- set name = '%s_%s' % (m.name, p.name) -*/
        /*- set array = p.array -*/
        /*- include "thread_local.c" -*/

        /*- if p.array -*/
            /*- set type = 'size_t' -*/
            /*- set name = '%s_%s_sz' % (m.name, p.name) -*/
            /*- set array = False -*/
            /*- include "thread_local.c" -*/
        /*- endif -*/
    /*- endfor -*/

static unsigned int /*? m.name ?*/_internal(void) {
    /* Unmarshal parameters */
    /*- set mr = c_symbol('mr') -*/
    unsigned int /*? mr ?*/ = 1; /* 0 contained the method index. */
    /*- for p in m.parameters -*/

        /*# Declare parameters. #*/
        /*- if p.array -*/
            size_t * /*? p.name ?*/_sz = get_/*? m.name ?*/_/*? p.name ?*/_sz();
        /*- endif -*/
        /*? show(p.type) ?*/ *
        /*- if p.array -*/
            *
        /*- endif -*/
        /*? p.name ?*/ = get_/*? m.name ?*/_/*? p.name ?*/();

        /*# Unmarshal parameters #*/
        /*- if p.direction.direction in ['in', 'inout'] -*/
            /*- if p.array -*/
                * /*? p.name ?*/_sz = seL4_GetMR(/*? mr ?*/);
                /*? mr ?*/ += 1;
                /*- set counter = c_symbol() -*/
                for (unsigned int /*? counter ?*/ = 0; /*? counter ?*/ < * /*? p.name ?*/_sz; /*? counter ?*/++) {
                    (* /*? p.name ?*/)[/*? counter ?*/] = seL4_GetMR(/*? mr ?*/);
                    /*? mr ?*/ += 1;
                    /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                        /* We need a second message register. */
                        (* /*? p.name ?*/)[/*? counter ?*/] |= ((/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE;
                        /*? mr ?*/ += 1;
                    /*- endif -*/
                }
            /*- else -*/
                _Static_assert(sizeof(/*? p.name ?*/) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/ does not fit in two message registers");
                * /*? p.name ?*/ = seL4_GetMR(/*? mr ?*/);
                /*? mr ?*/ += 1;
                /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                    /* We need a second message register. */
                    * /*? p.name ?*/ |= ((/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE;
                    /*? mr ?*/ += 1;
                /*- endif -*/
            /*- endif -*/
        /*- endif -*/

    /*- endfor -*/
    assert(/*? mr ?*/ <= seL4_MsgMaxLength &&
        "IPC buffer length exceeded during argument unmarshalling");

    /* Call the implementation */
    /*- if m.return_type -*/
        /*- set ret = c_symbol('ret') -*/
        /*? show(m.return_type) ?*/ /*? ret ?*/ =
    /*- endif -*/
    /*? me.to_interface.name ?*/_/*? m.name ?*/(
        /*- for p in m.parameters -*/
            /*- if p.array -*/
                /*- if p.direction.direction == 'in' -*/
                    *
                /*- endif -*/
                /*? p.name ?*/_sz,
                /*- if p.direction.direction == 'in' -*/
                    *
                /*- endif -*/
                /*? p.name ?*/
            /*- else -*/
                /*- if p.direction.direction == 'in' -*/
                    *
                /*- endif -*/
                /*? p.name ?*/
            /*- endif -*/
            /*- if not loop.last -*/,/*- endif -*/
        /*- endfor -*/
    );

    /* Marshal the response */
    /*? mr ?*/ = 0;
    /*- if m.return_type -*/
        _Static_assert(sizeof(/*? ret ?*/) <= 2 * sizeof(seL4_Word),
            "return type does not fit in two message registers");
        seL4_SetMR(/*? mr ?*/, /*? ret ?*/);
        /*? mr ?*/ += 1;
        /*- if sizeof(m.return_type) > __SIZEOF_POINTER__ -*/
            /* We need a second message register. */
            seL4_SetMR(/*? mr ?*/, /*? ret ?*/ >> __WORDSIZE);
            /*? mr ?*/ += 1;
        /*- endif -*/
    /*- endif -*/
    /*- for p in m.parameters -*/
        /*- if p.direction.direction in ['inout', 'out'] -*/
            /*- if p.array -*/
                seL4_SetMR(/*? mr ?*/, * /*? p.name ?*/_sz);
                /*? mr ?*/ += 1;
                /*- set counter = c_symbol() -*/
                for (unsigned int /*? counter ?*/ = 0; /*? counter ?*/ < * /*? p.name ?*/_sz; /*? counter ?*/++) {
                    seL4_SetMR(/*? mr ?*/, (* /*? p.name ?*/)[/*? counter ?*/]);
                    /*? mr ?*/ += 1;
                    /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                        /* We need a second message register. */
                        seL4_SetMR(/*? mr ?*/, (seL4_Word)((* /*? p.name ?*/)[/*? counter ?*/] >> __WORDSIZE));
                        /*? mr ?*/ += 1;
                    /*- endif -*/
                }
            /*- else -*/
                _Static_assert(sizeof(/*? p.name ?*/) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/ does not fit in two message registers");
                seL4_SetMR(/*? mr ?*/, * /*? p.name ?*/);
                /*? mr ?*/ += 1;
                /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                    /* We need a second message register. */
                    seL4_SetMR(/*? mr ?*/, (seL4_Word)(* /*? p.name ?*/ >> __WORDSIZE));
                    /*? mr ?*/ += 1;
                /*- endif -*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    return /*? mr ?*/;
}
/*- endfor -*/

/*- set info = c_symbol('info') -*/
/*- set first = c_symbol('first') -*/
static seL4_MessageInfo_t /*? me.to_interface.name ?*/__run_internal(bool /*? first ?*/, seL4_MessageInfo_t /*? info ?*/) {
    if (/*? first ?*/) {
        /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);
    }

    /* We should have at least been passed a method index */
    assert(seL4_MessageInfo_get_length(/*? info ?*/) >= 1);
    /*- set call = c_symbol('call') -*/
    int /*? call ?*/ = (int)seL4_GetMR(0);

    switch (/*? call ?*/) {
        /*- for i, m in enumerate(me.to_interface.type.methods) -*/
            case /*? i ?*/: { /*? '/' + '* ' + m.name + ' *' + '/' ?*/
                /*- set length = c_symbol('length') -*/
                unsigned int /*? length ?*/ = /*? m.name ?*/_internal();
                assert(/*? length ?*/ <= 120 &&
                    "IPC buffer length exceeded during argument marshalling");

                /* Send the response */
                /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /*? length ?*/);
                seL4_ReplyWait(/*? ep ?*/, /*? info ?*/, NULL);

                break;
            }
        /*- endfor -*/
        default: {
            /*# TODO: Handle error #*/
            assert(0);
        }
    }

    return /*? info ?*/;
}

int /*? me.to_interface.name ?*/__run(void) {
    /*- set first = c_symbol('first') -*/
    bool /*? first ?*/ = true;
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = { { 0 } };
    while (1) {
        /*? info ?*/ = /*? me.to_interface.name ?*/__run_internal(/*? first ?*/, /*? info ?*/);
        /*? first ?*/ = false;
    }
    return 0;
}
