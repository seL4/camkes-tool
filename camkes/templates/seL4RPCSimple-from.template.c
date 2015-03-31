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

/*- for i, m in enumerate(me.from_interface.type.methods) -*/

/*- set input_parameters = filter(lambda('x: x.direction.direction in [\'in\', \'inout\']'), m.parameters) -*/
static unsigned int /*? me.from_interface.name ?*/_/*? m.name ?*/_marshal(
    /*- for p in input_parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- else -*/
            /*? p.type.type ?*/
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
) {
    /*- set length = c_symbol('length') -*/
    unsigned int /*? length ?*/ = 0;

    /* Marshal the method index. */
    seL4_SetMR(/*? length ?*/, /*? i ?*/);
    /*? length ?*/++;

    /*- for p in input_parameters -*/
        seL4_SetMR(/*? length ?*/, (seL4_Word)/*? p.name ?*/);
        /*? length ?*/++;
        /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
            seL4_SetMR(/*? length ?*/, (seL4_Word)(((uint64_t)/*? p.name ?*/) >> __WORDSIZE));
            /*? length ?*/++;
            /*? assert(sizeof(p) <= 2 * __SIZEOF_POINTER__) ?*/
        /*- endif -*/
    /*- endfor -*/

    return /*? length ?*/;
}

static void /*? me.from_interface.name ?*/_/*? m.name ?*/_call(unsigned int length) {
    /* Call the endpoint */
    seL4_MessageInfo_t info = seL4_MessageInfo_new(0, 0, 0, length);
    (void)seL4_Call(/*? ep ?*/, info);
}

/*- set output_parameters = filter(lambda('x: x.direction.direction in [\'inout\', \'out\']'), m.parameters) -*/
static
/*- if m.return_type -*/
    /*? m.return_type.type ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/_unmarshal(
    /*- for p in output_parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- else -*/
            /*? p.type.type ?*/
        /*- endif -*/
        *
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
) {
    /*- set mr = c_symbol('mr') -*/
    unsigned int /*? mr ?*/ = 0;

    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type -*/
        /*? m.return_type.type ?*/ /*? ret ?*/ =
            (/*? m.return_type.type ?*/)seL4_GetMR(/*? mr ?*/);
        /*? mr ?*/++;
        /*- if sizeof(m.return_type) > __SIZEOF_POINTER__ -*/
            /*? ret ?*/ |=
                (/*? m.return_type.type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE);
            /*? mr ?*/++;
            /*? assert(sizeof(m.return_type) <= 2 * __SIZEOF_POINTER__) ?*/
        /*- endif -*/
    /*- endif -*/

    /*- for p in output_parameters -*/
        * /*? p.name ?*/ = (/*? p.type.type ?*/)seL4_GetMR(/*? mr ?*/);
        /*? mr ?*/++;
        /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
            * /*? p.name ?*/ |=
                (/*? p.type.type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) << __WORDSIZE);
            /*? mr ?*/++;
            /*? assert(sizeof(p) <= 2 * __SIZEOF_POINTER__) ?*/
        /*- endif -*/
    /*- endfor -*/

    /*- if m.return_type -*/
        return /*? ret ?*/;
    /*- endif -*/
}

/*- if m.return_type -*/
    /*? show(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/(
  /*- for p in m.parameters -*/
    /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' or p.direction.direction == 'refin' -*/
      /*? raise(NotImplementedError()) ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? ', '.join(map(show, m.parameters)) ?*/
) {
    /* Marshal input parameters. */
    /*- set mr = c_symbol('mr_index') -*/
    unsigned int /*? mr ?*/ = /*? me.from_interface.name ?*/_/*? m.name ?*/_marshal(
        /*- for p in input_parameters -*/
            /*- if p.direction.direction == 'inout' -*/
                *
            /*- endif -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /* Call the endpoint */
    /*? me.from_interface.name ?*/_/*? m.name ?*/_call(/*? mr ?*/);

    /* Unmarshal the response */
    /*- if m.return_type -*/
        /*- set ret = c_symbol('ret') -*/
        /*? m.return_type.type ?*/ /*? ret ?*/ =
    /*- endif -*/
    /*? me.from_interface.name ?*/_/*? m.name ?*/_unmarshal(
        /*- for p in output_parameters -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /*- if m.return_type -*/
        return /*? ret ?*/;
    /*- endif -*/
}
/*- endfor -*/
