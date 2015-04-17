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
      /*- if m.return_type and m.return_type.array -*/
        /*? raise(NotImplementedError()) ?*/
      /*- endif -*/
      /*- for p in m.parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' or p.direction == 'refin' -*/
          /*? raise(NotImplementedError()) ?*/
        /*- elif p.direction == 'in' -*/
          /*? show(p.type) ?*/ /*? p.name ?*/
        /*- else -*/
          /*? assert(p.direction in ['out', 'inout']) ?*/
          /*? show(p.type) ?*/ * /*? p.name ?*/
        /*- endif -*/
        /*- if not loop.last -*/
          ,
        /*- endif -*/
      /*- endfor -*/
    );
/*- endfor -*/

/*- set ep = alloc('ep', seL4_EndpointObject, read=True, write=True) -*/

/*# Necessary TLS variables #*/
/*- set threads = [1] + map(lambda('x: x + 2'), range(len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.emits + me.to_instance.type.consumes + me.to_instance.type.dataports))) -*/
/*- for m in me.to_interface.type.methods -*/
    /*- for p in m.parameters -*/
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

/*- set input_parameters = filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters) -*/
static void /*? me.to_interface.name ?*/_/*? m.name ?*/_unmarshal(
    /*- for p in input_parameters -*/
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
    unsigned int /*? mr ?*/ = 1; /* 0 contained the method index. */

    /*- for p in input_parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- elif sizeof(p) <= __SIZEOF_POINTER__ -*/
            * /*? p.name ?*/ = seL4_GetMR(/*? mr ?*/);
            /*? mr ?*/++;
        /*- else -*/
            * /*? p.name ?*/ = (/*? p.type.type ?*/)(((uint64_t)seL4_GetMR(/*? mr ?*/)) | (((uint64_t)seL4_GetMR(/*? mr ?*/ + 1)) << __WORDSIZE));
            /*? mr ?*/ += 2;
            /*? assert(sizeof(p) <= 2 * __SIZEOF_POINTER__) ?*/
        /*- endif -*/
    /*- endfor -*/
}

static
/*- if m.return_type -*/
    /*? m.return_type ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.to_interface.name ?*/_/*? m.name ?*/_invoke(
    /*- for p in m.parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- else -*/
            /*? p.type.type ?*/
        /*- endif -*/
        /*- if p.direction in ['inout', 'out'] -*/
            *
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
) {

    /* Call the implementation */
    /*- if m.return_type -*/
        return
    /*- endif -*/
    /*? me.to_interface.name ?*/_/*? m.name ?*/(
        /*- for p in m.parameters -*/
            /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
                /*? raise(NotImplementedError()) ?*/
            /*- endif -*/
            /*? p.name ?*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );
}

/*- set output_parameters = filter(lambda('x: x.direction in [\'inout\', \'out\']'), m.parameters) -*/
static unsigned int /*? me.to_interface.name ?*/_/*? m.name ?*/_marshal(
    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type -*/
        /*? m.return_type ?*/ /*? ret ?*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*- for p in output_parameters -*/
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
    /*- set mr = c_symbol('mr') -*/
    unsigned int /*? mr ?*/ = 0;

    /*- if m.return_type -*/
        seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? ret ?*/);
        /*? mr ?*/++;
        /*- if sizeof(m.return_type) > __SIZEOF_POINTER__ -*/
            seL4_SetMR(/*? mr ?*/, (seL4_Word)(((uint64_t)/*? ret ?*/) >> __WORDSIZE));
            /*? mr ?*/++;
            /*? assert(sizeof(m.return_type) <= 2 * __SIZEOF_POINTER__) ?*/
        /*- endif -*/
    /*- endif -*/

    /*- for p in output_parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- else -*/
            seL4_SetMR(/*? mr ?*/, (seL4_Word)/*? p.name ?*/);
            /*? mr ?*/++;
            /*- if sizeof(p) > __SIZEOF_POINTER__ -*/
                seL4_SetMR(/*? mr ?*/, (seL4_Word)(((uint64_t)/*? p.name ?*/) >> __WORDSIZE));
                /*? mr ?*/++;
                /*? assert(sizeof(p) <= 2 * __SIZEOF_POINTER__) ?*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    return /*? mr ?*/;
}

static unsigned int /*? me.to_interface.name ?*/_/*? m.name ?*/_internal(void) {
    /*- for p in m.parameters -*/
        /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
            /*? raise(NotImplementedError()) ?*/
        /*- else -*/
            /*? p.type.type ?*/
        /*- endif -*/
        *
        /*? p.name ?*/ = get_/*? m.name ?*/_/*? p.name ?*/();
    /*- endfor -*/

    /*? me.to_interface.name ?*/_/*? m.name ?*/_unmarshal(
        /*- for p in input_parameters -*/
            /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
                /*? raise(NotImplementedError()) ?*/
            /*- else -*/
                /*? p.name ?*/
            /*- endif -*/
            /*- if not loop.last -*/
                ,
            /*- endif -*/
        /*- endfor -*/
    );

    /*- set ret = c_symbol('ret') -*/
    /*- if m.return_type -*/
        /*? m.return_type ?*/ /*? ret ?*/ =
    /*- endif -*/
    /*? me.to_interface.name ?*/_/*? m.name ?*/_invoke(
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
    unsigned int /*? length ?*/ = /*? me.to_interface.name ?*/_/*? m.name ?*/_marshal(
        /*- if m.return_type -*/
            /*? ret ?*/
            /*- if len(output_parameters) > 0 -*/
                ,
            /*- endif -*/
        /*- endif -*/
        /*- for p in output_parameters -*/
            /*- if isinstance(p.type, camkes.ast.Reference) or p.array or p.type.type == 'string' -*/
                /*? raise(NotImplementedError()) ?*/
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
static seL4_MessageInfo_t /*? me.to_interface.name ?*/__run_internal(bool /*? first ?*/, seL4_MessageInfo_t /*? info ?*/) {
    /*- if not options.fcall_leave_reply_cap or len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.consumes + me.to_instance.type.mutexes + me.to_instance.type.semaphores) > 1 -*/
        /*- set result = c_symbol() -*/
        /*- set cnode = alloc_cap('cnode', my_cnode, write=True) -*/
        /*- set reply_cap_slot = alloc_cap('reply_cap_slot', None) -*/
    /*- endif -*/
    if (/*? first ?*/) {
        /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);

        /*- if not options.fcall_leave_reply_cap or len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.consumes + me.to_instance.type.mutexes + me.to_instance.type.semaphores) > 1 -*/
            int /*? result ?*/ UNUSED = seL4_CNode_SaveCaller(/*? cnode ?*/, /*? reply_cap_slot ?*/, 32);
            assert(/*? result ?*/ == 0);
        /*- endif -*/
    }

    /* We should have at least been passed a method index */
    assert(seL4_MessageInfo_get_length(/*? info ?*/) >= 1);
    /*- set call = c_symbol('call') -*/
    int /*? call ?*/ = (int)seL4_GetMR(0);

    switch (/*? call ?*/) {
        /*- for i, m in enumerate(me.to_interface.type.methods) -*/
            case /*? i ?*/: { /*? '/' + '* ' + m.name + ' *' + '/' ?*/
                /*- set length = c_symbol('length') -*/
                unsigned int /*? length ?*/ = /*? me.to_interface.name ?*/_/*? m.name ?*/_internal();

                /* Send the response */
                /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0, /*? length ?*/);

                /*- if not options.fcall_leave_reply_cap or len(me.to_instance.type.provides + me.to_instance.type.uses + me.to_instance.type.consumes + me.to_instance.type.mutexes + me.to_instance.type.semaphores) > 1 -*/
                    seL4_Send(/*? reply_cap_slot ?*/, /*? info ?*/);
                    /*? info ?*/ = seL4_Wait(/*? ep ?*/, NULL);
                    int /*? result ?*/ UNUSED = seL4_CNode_SaveCaller(/*? cnode ?*/, /*? reply_cap_slot ?*/, 32);
                    assert(/*? result ?*/ == 0);
                /*- else -*/
                    seL4_ReplyWait(/*? ep ?*/, /*? info ?*/, NULL);
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
