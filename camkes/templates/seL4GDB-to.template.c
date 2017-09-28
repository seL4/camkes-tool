/*#
 *# Copyright 2017, Data61
 *# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 *# ABN 41 687 119 230.
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(DATA61_BSD)
 #*/

#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sel4/sel4.h>
#include <sel4debug/debug.h>
#include <utils/util.h>
#include <camkes.h>
#include <stdarg.h>
#include <camkes/gdb/serial.h>
#include <camkes/gdb/gdb.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes, '../static/components/%s/' % me.instance.type.name) ?*/

/*- set methods_len = len(me.interface.type.methods) -*/
/*- set instance = me.instance.name -*/
/*- set interface = me.interface.name -*/
/*- set size = 'seL4_MsgMaxLength * sizeof(seL4_Word)' -*/
/*- set allow_trailing_data = False -*/
/*- set ep = alloc("ep_fault", seL4_EndpointObject, read=True, write=True, grant=True) -*/
/*- set cnode = alloc_cap('cnode', my_cnode, write=True) -*/
    /*- if options.realtime -*/
        /*- set reply_cap_slot = alloc('reply_cap_slot', seL4_RTReplyObject) -*/
    /*- else -*/
        /*- set reply_cap_slot = alloc_cap('reply_cap_slot', None) -*/
    /*- endif -*/
/*- set info = c_symbol('info') -*/

static gdb_state_t gdb_state;

static stop_reason_t find_stop_reason(seL4_Word fault_type, seL4_Word *args) {
    if (fault_type == seL4_Fault_DebugException) {
        seL4_Word exception_reason = args[1];
        ZF_LOGD("MR 0: %zX", args[0]);
        ZF_LOGD("MR 1: %zX", args[1]);
        ZF_LOGD("MR 2: %zX", args[2]);
        ZF_LOGD("MR 3: %zX", args[3]);
        ZF_LOGD("Breakpoint number %zu", args[1]);
        if (exception_reason == seL4_DataBreakpoint) {
            ZF_LOGD("Data breakpoint");
            gdb_state.stop_watch_addr = args[2];
            return stop_watch;
        } else if (exception_reason == seL4_InstructionBreakpoint) {
            ZF_LOGD("Hardware breakpoint");
            return stop_hw_break;
        } else if (exception_reason == seL4_SingleStep && gdb_state.current_thread_step_mode) {
            return stop_step;
        } else if (exception_reason == seL4_SoftwareBreakRequest) {
            ZF_LOGD("Decrementing fault ep because of seL4 kernel behavior");
            /* TODO This is a special case where the seL4 kernel gives us a fault instruction
               pointer that is no the faulting instruction.  We decrement the pc to correct for
               this.  In the future the kernel may end up changing the fault ip behavior and this
               decrement will then need to be removed to account for it.
             */
            gdb_state.current_pc--;
            delegate_write_register(gdb_state.current_thread_tcb, gdb_state.current_pc, 0);

            return stop_sw_break;
        } else {
            return stop_none;
        }
    } else {
        ZF_LOGE("Unknown fault type: %zd", fault_type);
        ZF_LOGE("MR 0: %zX", args[0]);
        ZF_LOGE("MR 1: %zX", args[1]);
        ZF_LOGE("MR 2: %zX", args[2]);
        ZF_LOGE("MR 3: %zX", args[3]);

        return stop_none;
    }
}

void /*? me.interface.name ?*/__init(void) {
    gdb_state.sem_post = b_post;
    gdb_state.current_thread_tcb = 1;
    serial_init(&gdb_state);
}

int /*? me.interface.name ?*/__run(void) {
    seL4_Word fault_type;
    seL4_Word length;
    seL4_MessageInfo_t info;
    seL4_Word args[4];
    seL4_Word reply_cap = /*? reply_cap_slot ?*/;
    while (1) {
        /* Wait for fault */
        info = seL4_Recv(/*? ep ?*/, &gdb_state.current_thread_tcb);
        /* Get the relevant registers */
        fault_type = seL4_MessageInfo_get_label(info);
        length = seL4_MessageInfo_get_length(info);
        for (int i = 0; i < length; i++) {
            args[i] = seL4_GetMR(i);
        }
        gdb_state.current_pc = args[0];
        ZF_LOGD("------------------------------");
        ZF_LOGD("Received fault for tcb %zu", gdb_state.current_thread_tcb);
        ZF_LOGD("Stopped at %zx", gdb_state.current_pc);
        ZF_LOGD("Length: %zu", length);
        // Save the reply cap
        seL4_CNode_SaveCaller(/*? cnode ?*/, reply_cap, 32);

        gdb_state.stop_reason = find_stop_reason(fault_type, args);
        gdb_state.current_thread_step_mode = false;

        /* Send fault message to gdb client */
        gdb_handle_fault(&gdb_state);

        /* Wait for gdb client to deal with fault */
        int UNUSED error = b_wait();

        /* Reply to the fault ep to restart the thread.
           We look inside the gdb_state struct to interpret how to restart the thread.
         */
        if (gdb_state.stop_reason == stop_step && gdb_state.current_thread_step_mode==false) {
            /* If this was a Debug Exception, then we respond with
               a bp_num and the number of instruction to step
               Since we're going to continue, we set MR0 to 0
             */
            info = seL4_MessageInfo_new(0, 0, 0, 1);
            seL4_SetMR(0, 0);
            seL4_Send(reply_cap, info);
        } else if (gdb_state.stop_reason == stop_none) {
            /* If this was a fault, set the instruction pointer to
               what we expect it to be
             */
            info = seL4_MessageInfo_new(0, 0, 0, 1);
            seL4_SetMR(0, gdb_state.current_pc);
            seL4_Send(reply_cap, info);
        } else {
            ZF_LOGD("Responding to some other debug exception %d", gdb_state.stop_reason);
            seL4_Signal(reply_cap);
        }

    }
    UNREACHABLE();
}

