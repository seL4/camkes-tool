/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*# C fragment that represents the base of the buffer used for storing IPC messages #*/
/*? assert(isinstance(base, six.string_types)) ?*/
/*? assert(isinstance(buffer_size, six.string_types)) ?*/
/*# Whether 'base' is a separate memory region instead of the thread's IPC buffer #*/
/*? assert(isinstance(userspace_ipc, bool)) ?*/
/*# Whether or not we trust our partner #*/
/*? assert(isinstance(trust_partner, bool)) ?*/

#include <sel4/sel4.h>
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sync/sem-bare.h>
#include <camkes/dataport.h>
#include <camkes/error.h>
#include <camkes/tls.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- set ep_obj = alloc_obj('ep', seL4_EndpointObject) -*/
/*- set ep = alloc_cap('ep_%s' % me.interface.name, ep_obj, write=True, grant=True) -*/

/*# Find any badges that have been explicitly assigned for this connection. That
 *# is, any badge identifiers that are not valid for us to assign automatically
 *# to other ends.
 #*/
/*- set used_badges = set() -*/
/*- for e in me.parent.from_ends -*/
  /*- set badge = configuration[e.instance.name].get('%s_attributes' % e.interface.name) -*/
  /*- if isinstance(badge, six.integer_types) -*/
    /*- do used_badges.add(badge) -*/
  /*- endif -*/
/*- endfor -*/

/*# Work out what badge each 'from' end of this connection would be given if no
 *# badges were specified with attributes. Note that we need to dodge any
 *# explicitly assigned badges.
 #*/
/*- set default_allocated_badges = [] -*/
/*- set next = [0] -*/
/*- for _ in me.parent.from_ends -*/
  /*- for _ in used_badges -*/
    /*- if next[0] in used_badges -*/
      /*- do next.__setitem__(0, next[0] + 1) -*/
    /*- endif -*/
  /*- endfor -*/
  /*? assert(next[0] not in used_badges) ?*/
  /*- do default_allocated_badges.append(next[0]) -*/
  /*- do next.__setitem__(0, next[0] + 1) -*/
/*- endfor -*/

/*# Now we're ready to determine the actual badge for this end. #*/
/*- set badge = configuration[me.instance.name].get('%s_attributes' % me.interface.name) -*/
/*- if isinstance(badge, six.integer_types) -*/
  /*- do cap_space.cnode[ep].set_badge(badge) -*/
/*- else -*/
  /*- do cap_space.cnode[ep].set_badge(default_allocated_badges[me.parent.from_ends.index(me)]) -*/
/*- endif -*/

/*- set BUFFER_BASE = c_symbol('BUFFER_BASE') -*/
#define /*? BUFFER_BASE ?*/ /*? base ?*/

/*- set methods_len = len(me.interface.type.methods) -*/
/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/
/*- set threads = list(six.moves.range(1, 2 + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes))) -*/

/* Interface-specific error handling */
/*- set error_handler = '%s_error_handler' % me.interface.name -*/
/*- include 'error-handler.c' -*/

/*# Conservative calculation of the numbers of threads in this component. #*/
/*- set thread_count = (1 if me.instance.type.control else 0) + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes) -*/

/*- set userspace_buffer_sem_value = c_symbol() -*/
/*- if thread_count > 1 and userspace_ipc -*/
  /*# If we have more than one thread and we're using a userspace memory window
   *# in lieu of the IPC buffer, multiple threads can end up racing on accesses
   *# to this window. To prevent this, we use a lock built on an endpoint.
   #*/
  /*- set userspace_buffer_ep = alloc('userspace_buffer_ep', seL4_EndpointObject, write=True, read=True) -*/
  static volatile int /*? userspace_buffer_sem_value ?*/ = 1;
/*- else -*/
  /*- set userspace_buffer_ep = None -*/
/*- endif -*/

/*- include 'array-typedef-check.c' -*/

int /*? me.interface.name ?*/__run(void) {
    /* This function is never actually executed, but we still emit it for the
     * purpose of type checking RPC parameters.
     */
    UNREACHABLE();

    /*# Check any typedefs we have been given are not arrays. #*/
    /*- include 'call-array-typedef-check.c' -*/
    return 0;
}

/*- for i, m in enumerate(me.interface.type.methods) -*/

/*- set name = m.name -*/
/*- set function = '%s_marshal_inputs' % m.name -*/
/*- set buffer = base -*/
/*- set size = buffer_size -*/
/*- set method_index = i -*/
/*- set input_parameters = list(filter(lambda('x: x.direction in [\'refin\', \'in\', \'inout\']'), m.parameters)) -*/
/*- include 'marshal-inputs.c' -*/

/*- set function = '%s_unmarshal_outputs' % m.name -*/
/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/
/*- set return_type = m.return_type -*/
/*- set allow_trailing_data = userspace_ipc -*/
/*- include 'unmarshal-outputs.c' -*/

/*- set ret_tls_var = c_symbol('ret_tls_var_from') -*/
/*- if m.return_type is not none -*/
  /*# We will need to take the address of a value representing this return
   *# value at some point. Construct a TLS variable.
   #*/
  /*- set name = ret_tls_var -*/
  /*- if m.return_type == 'string' -*/
    /*- set array = False -*/
    /*- set type = 'char*' -*/
    /*- include 'thread_local.c' -*/
  /*- else -*/
    /*- set array = False -*/
    /*- set type = macros.show_type(m.return_type) -*/
    /*- include 'thread_local.c' -*/
  /*- endif -*/
/*- endif -*/

/*- if m.return_type is not none -*/
    /*? macros.show_type(m.return_type) ?*/
/*- else -*/
    void
/*- endif -*/
/*? me.interface.name ?*/_/*? m.name ?*/(
/*- for p in m.parameters -*/
  /*- if p.direction == 'in' -*/
    /*- if p.array -*/
      size_t /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char **
      /*- else -*/
        const /*? macros.show_type(p.type) ?*/ *
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      const char *
    /*- else -*/
      /*? macros.show_type(p.type) ?*/
    /*- endif -*/
    /*? p.name ?*/
  /*- else -*/
    /*? assert(p.direction in ['refin', 'out', 'inout']) ?*/
    /*- if p.array -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      size_t * /*? p.name ?*/_sz,
      /*- if p.type == 'string' -*/
        char ***
      /*- else -*/
        /*? macros.show_type(p.type) ?*/ **
      /*- endif -*/
    /*- elif p.type == 'string' -*/
      char **
    /*- else -*/
      /*- if p.direction == 'refin' -*/
        const
      /*- endif -*/
      /*? macros.show_type(p.type) ?*/ *
    /*- endif -*/
    /*? p.name ?*/
  /*- endif -*/
  /*- if not loop.last -*/
    ,
  /*- endif -*/
/*- endfor -*/
/*- if len(m.parameters) == 0 -*/
  void
/*- endif -*/
) {

    /*- if len(me.parent.from_ends) == 1 and len(me.parent.to_ends) == 1 and len(me.parent.to_end.instance.type.provides + me.parent.to_end.instance.type.uses + me.parent.to_end.instance.type.consumes + me.parent.to_end.instance.type.mutexes + me.parent.to_end.instance.type.semaphores) <= 1 and options.fspecialise_syscall_stubs and methods_len == 1 and m.return_type is none and len(m.parameters) == 0 -*/
#ifdef ARCH_ARM
#ifndef __SWINUM
    #define __SWINUM(x) ((x) & 0x00ffffff)
#endif
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
            /*- if trust_partner -*/
                :"+r"(/*? dest ?*/)
                :[swinum]"i"(__SWINUM(seL4_SysCall)), "r"(/*? scno ?*/), "r"(/*? tag ?*/)
            /*- else -*/
                :"+r"(/*? dest ?*/), "+r"(/*? tag ?*/)
                :[swinum]"i"(__SWINUM(seL4_SysCall)), "r"(/*? scno ?*/)
                :"r2", "r3", "r4", "r5", "memory"
            /*- endif -*/
        );
        return;
#endif
    /*- endif -*/

    /*# We're about to start writing to the buffer. If relevant, protect our
     *# access.
     #*/
    /*- if userspace_buffer_ep is not none -*/
      camkes_protect_reply_cap();
      sync_sem_bare_wait(/*? userspace_buffer_ep ?*/,
        &/*? userspace_buffer_sem_value ?*/);
    /*- endif -*/

    /*- set ret_val = c_symbol('return') -*/
    /*- set ret_ptr = c_symbol('return_ptr') -*/
    /*- if m.return_type is not none -*/
      /*- if m.return_type == 'string' -*/
        char * /*? ret_val ?*/ UNUSED;
        char ** /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- else -*/
        /*? macros.show_type(m.return_type) ?*/ /*? ret_val ?*/ UNUSED;
        /*? macros.show_type(m.return_type) ?*/ * /*? ret_ptr ?*/ = TLS_PTR(/*? ret_tls_var ?*/, /*? ret_val ?*/);
      /*- endif -*/
    /*- endif -*/

    /*- if userspace_buffer_ep is none -*/
      /*# If `userspace_buffer_ep` is not `None` we've already protected the
       *# reply cap.
       #*/
      /* Save any pending reply cap as we'll eventually call seL4_Call which
       * could overwrite it. Note that we do this here before marshalling
       * parameters to ensure we don't inadvertently overwrite any marshalled
       * data with this call.
       */
      camkes_protect_reply_cap();
    /*- endif -*/

    /* Marshal all the parameters */
    /*- set function = '%s_marshal_inputs' % m.name -*/
    /*- set length = c_symbol('length') -*/
    unsigned /*? length ?*/ = /*- include 'call-marshal-inputs.c' -*/;
    if (unlikely(/*? length ?*/ == UINT_MAX)) {
        /* Error in marshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if m.return_type == 'string' -*/
                return NULL;
            /*- else -*/
                memset(/*? ret_ptr ?*/, 0, sizeof(* /*? ret_ptr ?*/));
                return * /*? ret_ptr ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    /* Call the endpoint */
    /*- set info = c_symbol('info') -*/
    seL4_MessageInfo_t /*? info ?*/ = seL4_MessageInfo_new(0, 0, 0,
        /*- if userspace_ipc -*/
                0
        /*- else -*/
                ROUND_UP_UNSAFE(/*? length ?*/, sizeof(seL4_Word)) / sizeof(seL4_Word)
        /*- endif -*/
        );
    /*? info ?*/ = seL4_Call(/*? ep ?*/, /*? info ?*/);

    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/ =
    /*- if userspace_ipc -*/
        /*? buffer_size ?*/;
    /*- else -*/
        seL4_MessageInfo_get_length(/*? info ?*/) * sizeof(seL4_Word);
        assert(/*? size ?*/ <= seL4_MsgMaxLength * sizeof(seL4_Word));
    /*- endif -*/

    /* Unmarshal the response */
    /*- set function = '%s_unmarshal_outputs' % m.name -*/
    /*- set return_type = m.return_type -*/
    /*- set err = c_symbol('error') -*/
    int /*? err ?*/ = /*- include 'call-unmarshal-outputs.c' -*/;
    if (unlikely(/*? err ?*/ != 0)) {
        /* Error in unmarshalling; bail out. */
        /*- if m.return_type is not none -*/
            /*- if m.return_type == 'string' -*/
                return NULL;
            /*- else -*/
                memset(/*? ret_ptr ?*/, 0, sizeof(* /*? ret_ptr ?*/));
                return * /*? ret_ptr ?*/;
            /*- endif -*/
        /*- else -*/
            return;
        /*- endif -*/
    }

    /*- if userspace_buffer_ep is not none -*/
      sync_sem_bare_post(/*? userspace_buffer_ep ?*/,
        &/*? userspace_buffer_sem_value ?*/);
    /*- endif -*/

    /*- if m.return_type is not none -*/
        return * /*? ret_ptr ?*/;
    /*- endif -*/
}
/*- endfor -*/
