/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*- set trust_partner = configuration[me.from_instance.name].get('trusted') == '"true"' -*/

/*- set base = '((void*)&seL4_GetIPCBuffer()->msg[0])' -*/
/*- set buffer = configuration[me.to_instance.name].get('%s_buffer' % me.to_interface.name) -*/
/*- if buffer is not none -*/
    extern void * /*? buffer ?*/;
/*- endif -*/
/*- set userspace_ipc = buffer is not none -*/
/*- set base = base if buffer is none else buffer -*/

/*- include 'rpc-connector-common-to.c' -*/

