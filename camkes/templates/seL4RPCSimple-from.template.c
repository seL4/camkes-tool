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
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/reg.h>
#include <utils/util.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/
/*? macros.show_includes(me.from_interface.type.includes, '../static/components/' + me.from_instance.type.name + '/') ?*/

/*- set ep = alloc('ep', seL4_EndpointObject, write=True, grant=True) -*/

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing to be done. */
    return 0;
}

/*# Used in TLS variable allocation below. #*/
/*- set threads = [1] + map(lambda('x: x + 2'), range(len(me.from_instance.type.provides + me.from_instance.type.uses + me.from_instance.type.emits + me.from_instance.type.consumes + me.from_instance.type.dataports))) -*/

/*- for i, m in enumerate(me.from_interface.type.methods) -*/

/*# For any array parameters, we need to allocate TLS variables. This is
 *# only the case for 'out' and 'inout' arrays, but we do it for any array for
 *# simplicity.
 #*/
/*- for p in m.parameters -*/
    /*# We've already set 'threads' previously. #*/
    /*- if p.array -*/
        /*- set type = 'size_t' -*/
        /*- set name = '%s_%s_sz' % (m.name, p.name) -*/
        /*- set array = False -*/
        /*- include "thread_local.c" -*/

        /*- set type = show(p.type) -*/
        /*- set name = '%s_%s' % (m.name, p.name) -*/
        /*- set array = True -*/
        /*- include "thread_local.c" -*/
    /*- endif -*/
/*- endfor -*/

/*- if m.return_type -*/
    /*? show(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/(
    /*? ', '.join(map(show, m.parameters)) ?*/
) {
    /*# Message register that we're currently marshalling into. #*/
    /*- set mr = c_symbol('mr_index') -*/
    unsigned int /*? mr ?*/ = 0;

    /* Marshal the method index */
    seL4_SetMR(/*? mr ?*/, /*? i ?*/);
    /*? mr ?*/ += 1;

    /* Marshal all the parameters */
    /*- for p in m.parameters -*/
        /*- if p.direction.direction == 'in' -*/
            /*- if p.array -*/
                _Static_assert(sizeof(/*? p.name ?*/[0]) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/'s members do not fit in two message registers");
                seL4_SetMR(/*? mr ?*/, /*? p.name ?*/_sz);
                /*? mr ?*/ += 1;
                /*- set counter = c_symbol() -*/
                for (unsigned int /*? counter ?*/ = 0; /*? counter ?*/ < /*? p.name ?*/_sz; /*? counter ?*/++) {
                    seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? p.name ?*/[/*? counter ?*/]);
                    /*? mr ?*/ += 1;
                    /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                        /* We need a second message register. */
                        seL4_SetMR(/*? mr ?*/, (seL4_Word)(/*? p.name ?*/[/*? counter ?*/] >> __WORDSIZE));
                        /*? mr ?*/ += 1;
                    /*- endif -*/
                }
            /*- else -*/
                _Static_assert(sizeof(/*? p.name ?*/) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/ does not fit in two message registers");
                seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? p.name ?*/);
                /*? mr ?*/ += 1;
                /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                    /* We need a second message register. */
                    seL4_SetMR(/*? mr ?*/, (seL4_Word)(/*? p.name ?*/ >> __WORDSIZE));
                    /*? mr ?*/ += 1;
                /*- endif -*/
            /*- endif -*/
        /*- elif p.direction.direction == 'inout' -*/
            /*- if p.array -*/
                _Static_assert(sizeof((* /*? p.name ?*/)[0]) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/'s members do not fit in two message registers");
                seL4_SetMR(/*? mr ?*/, * /*? p.name ?*/_sz);
                /*? mr ?*/ += 1;
                /*- set counter = c_symbol() -*/
                for (unsigned int /*? counter ?*/ = 0; /*? counter ?*/ < * /*? p.name ?*/_sz; /*? counter ?*/++) {
                    seL4_SetMR(/*? mr ?*/, (seL4_Word)(* /*? p.name ?*/)[/*? counter ?*/]);
                    /*? mr ?*/ += 1;
                    /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                        /* We need a second message register. */
                        seL4_SetMR(/*? mr ?*/, (seL4_Word)((* /*? p.name ?*/)[/*? counter ?*/] >> __WORDSIZE));
                        /*? mr ?*/ += 1;
                    /*- endif -*/
                }
            /*- else -*/
                _Static_assert(sizeof(* /*? p.name ?*/) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/ does not fit in two message registers");
                seL4_SetMR(/*? mr ?*/, (seL4_Word)(* /*? p.name ?*/));
                /*? mr ?*/ += 1;
                /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                    /* We need a second message register. */
                    seL4_SetMR(/*? mr ?*/, (seL4_Word)(* /*? p.name ?*/ >> __WORDSIZE));
                    /*? mr ?*/ += 1;
                /*- endif -*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/
    assert(/*? mr ?*/ <= seL4_MsgMaxLength &&
        "IPC buffer length exceeded during argument marshalling");

    /* Call the endpoint */
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /*? mr ?*/);
    (void)seL4_Call(/*? ep ?*/, /*? info ?*/);

    /* Unmarshal the response */
    /*? mr ?*/ = 0;
    /*- if m.return_type -*/
        /*- set ret = c_symbol('ret') -*/
        /*? show(m.return_type) ?*/ /*? ret ?*/ = (/*? show(m.return_type) ?*/)seL4_GetMR(/*? mr ?*/);
        /*? mr ?*/ += 1;
        /*- if sizeof(m.return_type) > __SIZEOF_POINTER__ -*/
            /* We need a second message register. */
            /*? ret ?*/ |= ((/*? show(m.return_type) ?*/)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE;
            /*? mr ?*/ += 1;
        /*- endif -*/
        _Static_assert(sizeof(/*? ret ?*/) <= 2 * sizeof(seL4_Word),
            "return value does not fit in two message registers");
    /*- endif -*/

    /*- for p in m.parameters -*/
        /*- if p.direction.direction in ['out', 'inout'] -*/
            /*- if p.array -*/
                * /*? p.name ?*/_sz = seL4_GetMR(/*? mr ?*/);
                /*? mr ?*/ += 1;
                * /*? p.name ?*/ = *get_/*? m.name ?*/_/*? p.name ?*/();
                /*- set counter = c_symbol() -*/
                for (unsigned int /*? counter ?*/ = 0; /*? counter ?*/ < * /*? p.name ?*/_sz; /*? counter ?*/++) {
                    (* /*? p.name ?*/)[/*? counter ?*/] = (/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/);
                    /*? mr ?*/ += 1;
                    /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                        /* We need a second message register. */
                        (* /*? p.name ?*/)[/*? counter ?*/] |= ((/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE;
                        /*? mr ?*/ += 1;
                    /*- endif -*/
                }
            /*- else -*/
                _Static_assert(sizeof(* /*? p.name ?*/) <= 2 * sizeof(seL4_Word),
                    "parameter /*? p.name ?*/ does not fit in two message registers");
                * /*? p.name ?*/ = (/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/);
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

    /*- if m.return_type -*/
        return /*? ret ?*/;
    /*- endif -*/
}
/*- endfor -*/
