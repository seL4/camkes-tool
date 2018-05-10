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
#include <sel4/sel4.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/reg.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*# HACK: The CapDL verification is based on a future, proposed version of
 *# seL4, wherein only Write is required on an endpoint to call to it. This
 *# allows a more principled information flow analysis.
 *#
 *# To get around this mess, we detect if the user is targeting the CapDL
 *# verification and, if so, do not provide Grant on this capability. Note that
 *# the resulting system will not run correctly.
 #*/
/*- if os.environ.get('CONFIG_CAMKES_LABEL_MAPPING', '') == 'y' -*/
  /*- set grant = False -*/
/*- else -*/
  /*- set grant = True -*/
/*- endif -*/
/*- set ep = alloc('ep', seL4_EndpointObject, write=True, grant=grant) -*/

/*- for i, m in enumerate(me.interface.type.methods) -*/

/*- set input_parameters = list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters)) -*/
static unsigned /*? me.interface.name ?*/_/*? m.name ?*/_marshal(
    /*- for p in input_parameters -*/
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
    /*- if len(input_parameters) == 0 -*/
        void
    /*- endif -*/
) {
    /*- set length = c_symbol('length') -*/
    unsigned /*? length ?*/ = 0;

    /* Marshal the method index. */
    seL4_SetMR(/*? length ?*/, /*? i ?*/);
    /*? length ?*/++;

    /*- for p in input_parameters -*/
        seL4_SetMR(/*? length ?*/, (seL4_Word)/*? p.name ?*/);
        /*? length ?*/++;
        /*- if macros.sizeof(options.architecture, p) > macros.sizeof(options.architecture, 'void*') -*/
            seL4_SetMR(/*? length ?*/, (seL4_Word)(((uint64_t)/*? p.name ?*/) >> __WORDSIZE));
            /*? length ?*/++;
            /*? assert(macros.sizeof(options.architecture, p) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
        /*- endif -*/
    /*- endfor -*/

    return /*? length ?*/;
}

static void /*? me.interface.name ?*/_/*? m.name ?*/_call(unsigned length) {
    /* Call the endpoint */
    seL4_MessageInfo_t info = seL4_MessageInfo_new(0, 0, 0, length);
    (void)seL4_Call(/*? ep ?*/, info);
}

/*- set output_parameters = list(filter(lambda('x: x.direction in [\'inout\', \'out\']'), m.parameters)) -*/
static
/*- if m.return_type is not none -*/
    /*? m.return_type ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.interface.name ?*/_/*? m.name ?*/_unmarshal(
    /*- for p in output_parameters -*/
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
    /*- if len(output_parameters) == 0 -*/
        void
    /*- endif -*/
) {
    /*- set mr = c_symbol('mr') -*/
    unsigned /*? mr ?*/ UNUSED = 0;

    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type is not none -*/
        /*? m.return_type ?*/ /*? ret ?*/ =
            (/*? m.return_type ?*/)seL4_GetMR(/*? mr ?*/);
        /*? mr ?*/++;
        /*- if macros.sizeof(options.architecture, m.return_type) > macros.sizeof(options.architecture, 'void*') -*/
            /*? ret ?*/ |=
                (/*? m.return_type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE);
            /*? mr ?*/++;
            /*? assert(macros.sizeof(options.architecture, m.return_type) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
        /*- endif -*/
    /*- endif -*/

    /*- for p in output_parameters -*/
        * /*? p.name ?*/ = (/*? p.type ?*/)seL4_GetMR(/*? mr ?*/);
        /*? mr ?*/++;
        /*- if macros.sizeof(options.architecture, p) > macros.sizeof(options.architecture, 'void*') -*/
            * /*? p.name ?*/ |=
                (/*? p.type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE);
            /*? mr ?*/++;
            /*? assert(macros.sizeof(options.architecture, p) <= 2 * macros.sizeof(options.architecture, 'void*')) ?*/
        /*- endif -*/
    /*- endfor -*/

    /*- if m.return_type is not none -*/
        return /*? ret ?*/;
    /*- endif -*/
}

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
    /*? macros.show_type(p.type) ?*/
  /*- else -*/
    /*? assert(p.direction in ['out', 'inout']) ?*/
    /*? macros.show_type(p.type) ?*/ *
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
    /* Save any pending reply cap, as we'll overwrite it during `seL4_Call`. */
    camkes_protect_reply_cap();

    /* Marshal input parameters. */
    /*- set mr = c_symbol('mr_index') -*/
    unsigned /*? mr ?*/ = /*? me.interface.name ?*/_/*? m.name ?*/_marshal(
        /*- for p in input_parameters -*/
            /*- if p.direction == 'inout' -*/
                *
            /*- endif -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /* Call the endpoint */
    /*? me.interface.name ?*/_/*? m.name ?*/_call(/*? mr ?*/);

    /* Unmarshal the response */
    /*- if m.return_type is not none -*/
        /*- set ret = c_symbol('ret') -*/
        /*? m.return_type ?*/ /*? ret ?*/ =
    /*- endif -*/
    /*? me.interface.name ?*/_/*? m.name ?*/_unmarshal(
        /*- for p in output_parameters -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /*- if m.return_type is not none -*/
        return /*? ret ?*/;
    /*- endif -*/
}
/*- endfor -*/
