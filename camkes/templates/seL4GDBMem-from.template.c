/*#
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 #*/

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes, '../static/components/%s/' % me.instance.type.name) ?*/

/*- set thread_caps = [] -*/
/*- set mem_ep = alloc("mem_fault", seL4_EndpointObject, read=True, write=True, grantreply=True) -*/

/*- for cap in cap_space.cnode: -*/
    /*- if isinstance(cap_space.cnode[cap].referent, capdl.TCB): -*/
        /*- set cap_name = cap_space.cnode[cap].referent.name-*/
        /*- do thread_caps.append((cap, cap_name)) -*/
    /*- endif -*/
/*- endfor -*/
/*- for cap, cap_name in thread_caps: -*/
     /*- if "GDB_delegate" in cap_name: -*/
         /*- do cap_space.cnode[mem_ep].set_badge(cap) -*/
        /*- do cap_space.cnode[cap].referent.set_fault_ep_slot(mem_ep) -*/
     /*- endif -*/
/*- endfor -*/
