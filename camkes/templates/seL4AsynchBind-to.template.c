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
#include <sel4/sel4.h>

/*? macros.show_includes(me.to_instance.type.includes) ?*/

/*- set aep = alloc('aep', seL4_AsyncEndpointObject, read=True, write=True) -*/

seL4_CPtr /*? me.to_interface.name ?*/_aep(void) {
    return /*? aep ?*/;
}
