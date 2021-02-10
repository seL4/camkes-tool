/*#
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 #*/

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes, '../static/components/%s/' % me.instance.type.name) ?*/


/*- set mem_ep = alloc("mem_fault", seL4_EndpointObject, read=True, write=True, grantreply=True) -*/

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

int /*? me.interface.name ?*/__run(void) {
    // Make connection to gdb
    seL4_Word delegate_tcb;
    seL4_UserContext regs;
    while (1) {
        seL4_Recv(/*? mem_ep ?*/, &delegate_tcb);
        seL4_TCB_ReadRegisters(delegate_tcb, false, 0,
                               sizeof(seL4_UserContext) / sizeof(seL4_Word),
                               &regs);
        // Check eax is 0 so that we know they were checking memory
        // TODO Add a check on pc to see if they were in the mem check function
        if (regs.eax == 0) {
            // Signal to the delegate the memory is invalid
            regs.eax = 1;
               // Increment past the faulting instruction
            regs.eip += 2;
            // Write registers back
            seL4_TCB_WriteRegisters(delegate_tcb, false, 0,
                                    sizeof(seL4_UserContext) / sizeof(seL4_Word),
                                    &regs);
            // Resume the caller
            seL4_MessageInfo_t info = seL4_MessageInfo_new(0, 0, 0, 1);
            seL4_SetMR(0, regs.eip);
            seL4_Reply(info);
        }
    }
}
