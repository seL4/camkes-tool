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

#include <assert.h>
#include <camkes/tls.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sel4/sel4.h>
#include <sys/reg.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- for m in me.interface.type.methods -*/
    extern
    /*- if m.return_type is not none -*/
        /*? macros.show_type(m.return_type) ?*/
    /*- else -*/
        void
    /*- endif -*/
    /*? me.interface.name ?*/_/*? m.name ?*/(
      /*- for p in m.parameters -*/
        /*- if p.array or p.type == 'string' or p.direction == 'refin' -*/
          /*? raise(TemplateError('unsupported')) ?*/
        /*- elif p.direction == 'in' -*/
          /*? macros.show_type(p.type) ?*/ /*? p.name ?*/
        /*- else -*/
          /*? assert(p.direction in ['out', 'inout']) ?*/
          /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
        /*- endif -*/
        /*- if not loop.last -*/
          ,
        /*- endif -*/
      /*- endfor -*/
      /*- if len(m.parameters) == 0 -*/
        void
      /*- endif -*/
    );
/*- endfor -*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

/*# We may need a slot to save reply caps in. #*/
/*- if len(me.instance.type.provides + me.instance.type.uses + me.instance.type.consumes + me.instance.type.mutexes + me.instance.type.semaphores) > 1 -*/
    /*- set cnode = alloc_cap('cnode', my_cnode, write=True) -*/
    /*- set reply_cap_slot = alloc_cap('reply_cap_slot', None) -*/
/*- endif -*/

/*# Necessary TLS variables #*/
/*- set threads = [1] + list(map(lambda('x: x + 2'), range(len(me.instance.type.provides + me.instance.type.uses + me.instance.type.emits + me.instance.type.consumes + me.instance.type.dataports)))) -*/
/*- for m in me.interface.type.methods -*/
    /*- for p in m.parameters -*/
        /*- set type = macros.show_type(p.type) -*/
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

/*- set input_parameters = list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters)) -*/
static void /*? me.interface.name ?*/_/*? m.name ?*/_unmarshal(
    /*- for p in input_parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- else -*/
            /*? p.type ?*/
        /*- endif -*/
        *
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    /*- if len(input_parameters) == 0 -*/
        void
    /*- endif -*/
) {
    /*- set mr = c_symbol('mr') -*/
    unsigned /*? mr ?*/ UNUSED = 1; /* 0 contained the method index. */

    /*- for p in input_parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- elif macros.sizeof(options.architecture, p) <= macros.sizeof(options.architecture, 'void*') -*/
            * /*? p.name ?*/ = seL4_GetMR(/*? mr ?*/);
            /*? mr ?*/++;
        /*- else -*/
            * /*? p.name ?*/ = (/*? p.type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) | (((uint64_t)seL4_GetMR(/*? mr ?*/ + 1)) << __WORDSIZE));
            /*? mr ?*/ += 2;
            /*? assert(macros.sizeof(options.architecture, p) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
        /*- endif -*/
    /*- endfor -*/
}

static
/*- if m.return_type is not none -*/
    /*? m.return_type ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.interface.name ?*/_/*? m.name ?*/_invoke(
    /*- for p in m.parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- else -*/
            /*? p.type ?*/
        /*- endif -*/
        /*- if p.direction in ['inout', 'out'] -*/
            *
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    /*- if len(m.parameters) == 0 -*/
        void
    /*- endif -*/
) {

    /* Call the implementation */
    /*- if m.return_type is not none -*/
        return
    /*- endif -*/
    /*? me.interface.name ?*/_/*? m.name ?*/(
        /*- for p in m.parameters -*/
            /*- if p.array or p.type == 'string' -*/
                /*? raise(TemplateError('unsupported')) ?*/
            /*- endif -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );
}

/*- set output_parameters = list(filter(lambda('x: x.direction in [\'inout\', \'out\']'), m.parameters)) -*/
static unsigned /*? me.interface.name ?*/_/*? m.name ?*/_marshal(
    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type is not none -*/
        /*? m.return_type ?*/ /*? ret ?*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*- for p in output_parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- else -*/
            /*? p.type ?*/
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    /*- if m.return_type is none and len(output_parameters) == 0 -*/
        void
    /*- endif -*/
) {
    /*- set mr = c_symbol('mr') -*/
    unsigned /*? mr ?*/ = 0;

    /*- if m.return_type is not none -*/
        seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? ret ?*/);
        /*? mr ?*/++;
        /*- if macros.sizeof(options.architecture, m.return_type) > macros.sizeof(options.architecture, 'void*') -*/
            seL4_SetMR(/*? mr ?*/, (seL4_Word)(((uint64_t)/*? ret ?*/) >> __WORDSIZE));
            /*? mr ?*/++;
            /*? assert(macros.sizeof(options.architecture, m.return_type) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
        /*- endif -*/
    /*- endif -*/

    /*- for p in output_parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- else -*/
            seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? p.name ?*/);
            /*? mr ?*/++;
            /*- if macros.sizeof(options.architecture, p) > macros.sizeof(options.architecture, 'void*') -*/
                seL4_SetMR(/*? mr ?*/, (seL4_Word)(((uint64_t)/*? p.name ?*/) >> __WORDSIZE));
                /*? mr ?*/++;
                /*? assert(macros.sizeof(options.architecture, p) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    return /*? mr ?*/;
}

static unsigned /*? me.interface.name ?*/_/*? m.name ?*/_internal(void) {
    /*- for p in m.parameters -*/
        /*- if p.array or p.type == 'string' -*/
            /*? raise(TemplateError('unsupported')) ?*/
        /*- else -*/
            /*? p.type ?*/
        /*- endif -*/
        *
        /*? p.name ?*/ = get_/*? m.name ?*/_/*? p.name ?*/();
    /*- endfor -*/

    /*? me.interface.name ?*/_/*? m.name ?*/_unmarshal(
        /*- for p in input_parameters -*/
            /*- if p.array or p.type == 'string' -*/
                /*? raise(TemplateError('unsupported')) ?*/
            /*- else -*/
                /*? p.name ?*/
            /*- endif -*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /*- if len(me.instance.type.provides + me.instance.type.uses + me.instance.type.consumes + me.instance.type.mutexes + me.instance.type.semaphores) > 1 -*/
        /*- set result = c_symbol() -*/

        int /*? result ?*/ UNUSED = seL4_CNode_SaveCaller(/*? cnode ?*/, /*? reply_cap_slot ?*/, 32);
        assert(/*? result ?*/ == 0);
    /*- endif -*/

    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type is not none -*/
        /*? m.return_type ?*/ /*? ret ?*/ =
    /*- endif -*/
    /*? me.interface.name ?*/_/*? m.name ?*/_invoke(
        /*- for p in m.parameters -*/
            /*- if p.direction == 'in' -*/
                * /*? p.name ?*/
            /*- else -*/
                /*? p.name ?*/
            /*- endif -*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /*- set length = c_symbol('length') -*/
    unsigned /*? length ?*/ = /*? me.interface.name ?*/_/*? m.name ?*/_marshal(
        /*- if m.return_type is not none -*/
            /*? ret ?*/
            /*- if len(output_parameters) > 0 -*/
                ,
            /*- endif -*/
        /*- endif -*/
        /*- for p in output_parameters -*/
            /*- if p.array or p.type == 'string' -*/
                /*? raise(TemplateError('unsupported')) ?*/
            /*- else -*/
                * /*? p.name ?*/
            /*- endif -*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    return /*? length ?*/;
}
/*- endfor -*/

/*- set info = c_symbol('info') -*/
/*- set first = c_symbol('first') -*/
static seL4_MessageInfo_t /*? me.interface.name ?*/__run_internal(bool /*? first ?*/, seL4_MessageInfo_t /*? info ?*/) {
    if (/*? first ?*/) {
        /*? info ?*/ = seL4_Recv(/*? ep ?*/, NULL);
    }

    /* We should have at least been passed a method index */
    assert(seL4_MessageInfo_get_length(/*? info ?*/) >= 1);
    /*- set call = c_symbol('call') -*/
    int /*? call ?*/ = (int)seL4_GetMR(0);

    switch (/*? call ?*/) {
        /*- for i, m in enumerate(me.interface.type.methods) -*/
            case /*? i ?*/: { /*? '%s%s%s%s%s' % ('/', '* ', m.name, ' *', '/') ?*/
                /*- set length = c_symbol('length') -*/
                unsigned /*? length ?*/ = /*? me.interface.name ?*/_/*? m.name ?*/_internal();

                /* Send the response */
                /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /*? length ?*/);

                /*- if len(me.instance.type.provides + me.instance.type.uses + me.instance.type.consumes + me.instance.type.mutexes + me.instance.type.semaphores) > 1 -*/
                    seL4_Send(/*? reply_cap_slot ?*/, /*? info ?*/);
                    /*? info ?*/ = seL4_Recv(/*? ep ?*/, NULL);
                /*- else -*/
                    seL4_ReplyRecv(/*? ep ?*/, /*? info ?*/, NULL);
                /*- endif -*/

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

int /*? me.interface.name ?*/__run(void) {
    /*- set first = c_symbol('first') -*/
    bool /*? first ?*/ = true;
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = { { 0 } };
    while (1) {
        /*? info ?*/ = /*? me.interface.name ?*/__run_internal(/*? first ?*/, /*? info ?*/);
        /*? first ?*/ = false;
    }
    return 0;
}
