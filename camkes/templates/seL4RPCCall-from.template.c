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
#include <sel4/sel4.h>
#include <assert.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sync/sem-bare.h>
#include <camkes/marshal.h>
#include <camkes/dataport.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/
/*? macros.show_includes(me.from_interface.type.includes, '../static/components/' + me.from_instance.type.name + '/') ?*/

/*- set ep = alloc('ep', seL4_EndpointObject, write=True, grant=True) -*/
/*- for s in configuration.settings -*/
    /*- if s.instance == me.from_instance.name -*/
        /*- if s.attribute == "%s_attributes" % (me.from_interface.name) -*/
            /*- set badge = s.value.strip('"') -*/
            /*- do cap_space.cnode[ep].set_badge(int(badge, 0)) -*/
        /*- endif -*/
    /*- endif -*/
/*- endfor -*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
/*- set base = '((void*)&seL4_GetIPCBuffer()->msg[0])' -*/
/*- set userspace_ipc = False -*/
/*- if configuration -*/
    /*- set buffers = filter(lambda('x: x.instance == \'%s\' and x.attribute == \'%s_buffer\'' % (me.from_instance.name, me.from_interface.name)), configuration.settings) -*/
    /*- if len(buffers) == 1 -*/
        /*- set base = buffers[0].value -*/
        /*- set userspace_ipc = True -*/
        extern void * /*? base ?*/;
    /*- endif -*/
/*- endif -*/
#define /*? BUFFER_BASE ?*/ /*? base ?*/

/*# Conservative calculation of the numbers of threads in this component. #*/
/*- set threads = (1 if me.from_instance.type.control else 0) + len(me.from_instance.type.provides) + len(me.from_instance.type.uses) + len(me.from_instance.type.emits) + len(me.from_instance.type.consumes) -*/

/*- set userspace_buffer_ep = [None] -*/
/*- set userspace_buffer_sem_value = c_symbol() -*/
/*- if threads > 1 and userspace_ipc -*/
  /*# If we have more than one thread and we're using a userspace memory window
   *# in lieu of the IPC buffer, multiple threads can end up racing on accesses
   *# to this window. To prevent this, we use a lock built on an endpoint.
   #*/
  /*- do userspace_buffer_ep.__setitem__(0, alloc('userspace_buffer_ep', seL4_EndpointObject, write=True, read=True)) -*/
  static volatile int /*? userspace_buffer_sem_value ?*/ = 1;
/*- endif -*/
/*- set userspace_buffer_ep = userspace_buffer_ep[0] -*/

int /*? me.from_interface.name ?*/__run(void) {
    /* No setup required */
    return 0;
}

/*- for i, m in enumerate(me.from_interface.type.methods) -*/
/*- if m.return_type -*/
    /*? show(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.from_interface.name ?*/_/*? m.name ?*/(
    /*? ', '.join(map(show, m.parameters)) ?*/
) {
    /*- set methods_len = len(me.from_interface.type.methods) -*/

    /*# The optimisation below is only valid to perform if we do not have any
     *# reference (typedefed C) types.
     #*/
    /*- set contains_reference_type = [False] -*/
    /*- for p in m.parameters -*/
      /*- if isinstance(p.type, camkes.ast.Reference) -*/
        /*- do contains_reference_type.__setitem__(0, True) -*/
        /*- break -*/
      /*- endif -*/
    /*- endfor -*/

    /*- if options.fspecialise_syscall_stubs and not contains_reference_type[0] and len(filter(lambda('x: x.array or x.type.type == \'string\''), m.parameters)) == 0 -*/
#ifdef ARCH_ARM
#ifndef __SWINUM
    #define __SWINUM(x) ((x) & 0x00ffffff)
#endif
        /*- if methods_len == 1 and not m.return_type and len(m.parameters) == 0 -*/
            /* We don't need to send or return any information because this
             * is the only method in this interface and it has no parameters or
             * return value. We can use an optimised syscall stub and take an
             * early exit.
             *
             * To explain where this stub deviates from the standard Call stub:
             *  - No asm clobbers because we're not receiving any arguments in
             *    the reply (that would usually clobber r2-r5);
             *  - Message info as an input only because we know the return info
             *    will be identical, so the compiler can avoid reloading it if
             *    we need the value after the syscall; and
             *  - Setup r7 and r1 first because they are preserved across the
             *    syscall and this helps the compiler emit a backwards branch
             *    to create a tight loop if we're calling this interface
             *    repeatedly.
             */
            /*- set scno = c_symbol() -*/
            register seL4_Word /*? scno ?*/ asm("r7") = seL4_SysCall;
            /*- set tag = c_symbol() -*/
            register seL4_MessageInfo_t /*? tag ?*/ asm("r1") = seL4_MessageInfo_new(0, 0, 0, 0);
            /*- set dest = c_symbol() -*/
            register seL4_Word /*? dest ?*/ asm("r0") = /*? ep ?*/;
            asm volatile("swi %[swinum]"
                :"+r"(/*? dest ?*/)
                :[swinum]"i"(__SWINUM(seL4_SysCall)), "r"(/*? scno ?*/), "r"(/*? tag ?*/)
            );
            return;
        /*- endif -*/
#endif
    /*- endif -*/

    /*# We're about to start writing to the buffer. If relevant, protect our
     *# access.
     #*/
    /*- if userspace_buffer_ep -*/
      sync_sem_bare_wait(/*? userspace_buffer_ep ?*/,
        &/*? userspace_buffer_sem_value ?*/);
    /*- endif -*/

    /* Marshal the method index */
    /*- set offset = ['0'] -*/
    /*- if methods_len > 1 -*/
        /*- if methods_len <= 2 ** 8 -*/
            uint8_t
        /*- elif methods_len <= 2 ** 16 -*/
            uint16_t
        /*- elif methods_len <= 2 ** 32 -*/
            uint32_t
        /*- else -*/
            /*? raise(Exception('too many methods in interface %s' % me.from_interface.type.name)) ?*/
        /*- endif -*/
        /*- set call = c_symbol('call') -*/
        /*? call ?*/ = /*? i ?*/;
        memcpy(/*? BUFFER_BASE ?*/, &/*? call ?*/, sizeof(/*? call ?*/));
        /*- do offset.append('sizeof(%s)' % call) -*/
    /*- endif -*/

    /* Marshal all the parameters */
    /*- for p in m.parameters -*/
        /*- if p.direction.direction in ['inout', 'in'] -*/
            /*- if p.array -*/
                /*- set lcount = c_symbol() -*/
                for (int /*? lcount ?*/ = 0; /*? lcount ?*/ <
                    /*- if p.direction.direction == 'inout' -*/
                        *
                    /*- endif -*/
                    /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
                    memcpy(/*? BUFFER_BASE ?*/ + /*? '+'.join(offset) ?*/ + /*? lcount ?*/ * sizeof(/*? show(p.type) ?*/), &((
                        /*- if p.direction.direction == 'inout' -*/
                            *
                        /*- endif -*/
                        /*? p.name ?*/)[/*? lcount ?*/]), sizeof(/*? show(p.type) ?*/));
                }
                /*- do offset.append('(%s%s_sz) * sizeof(%s)' % ('*' if p.direction.direction == 'inout' else '', p.name, show(p.type))) -*/
            /*- elif p.type.type == 'string' -*/
                /*- set ptr = c_symbol() -*/
                char * /*? ptr ?*/ UNUSED = stpcpy((char*)((uint32_t)/*? BUFFER_BASE ?*/ + /*? '+'.join(offset) ?*/), /*? p.name ?*/);
                /*- do offset.append('(uint32_t)%s + 1 - (uint32_t)%s - %s' % (ptr, BUFFER_BASE, '-'.join(offset))) -*/
            /*- else -*/
                memcpy(/*? BUFFER_BASE ?*/ + /*? '+'.join(offset) ?*/,
                /*- if p.direction.direction == 'in' -*/
                    &
                /*- endif -*/
                /*? p.name ?*/, sizeof(/*? show(p.type) ?*/));
                /*- do offset.append('sizeof(%s)' % show(p.type)) -*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    /* Call the endpoint */
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0,
        /*- if userspace_ipc -*/
                0
        /*- else -*/
                ROUND_UP(/*? '+'.join(offset) ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word)
        /*- endif -*/
        );
    (void)seL4_Call(/*? ep ?*/, /*? info ?*/);

    /* Unmarshal the response */
    /*- set buffer = c_symbol('buffer') -*/
    void * /*? buffer ?*/ UNUSED = /*? BUFFER_BASE ?*/;
    /*- if m.return_type -*/
        /*- set ret = c_symbol('ret') -*/
        /*? show(m.return_type) ?*/ /*? ret ?*/;
        /*- if m.return_type.type == 'string' -*/
            /*? macros.unmarshal_string(buffer, ret, True) ?*/
        /*- else -*/
            /*? macros.unmarshal(buffer, ret, 'sizeof(%s)' % show(m.return_type)) ?*/
        /*- endif -*/
    /*- endif -*/

    /*- for p in m.parameters -*/
        /*- if p.direction.direction in ['inout', 'out'] -*/
            /*- if p.array -*/
                /*? macros.unmarshal_array(buffer, p.name, 'sizeof(%s)' % show(p.type), True, show(p.type)) ?*/
            /*- elif p.type.type == 'string' -*/
                /*? macros.unmarshal_string(buffer, p.name) ?*/
            /*- else -*/
                /*? macros.unmarshal(buffer, p.name, 'sizeof(%s)' % show(p.type), True) ?*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    /*- if userspace_buffer_ep -*/
      sync_sem_bare_post(/*? userspace_buffer_ep ?*/,
        &/*? userspace_buffer_sem_value ?*/);
    /*- endif -*/

    /*- if m.return_type -*/
        return /*? ret ?*/;
    /*- endif -*/
}
/*- endfor -*/
