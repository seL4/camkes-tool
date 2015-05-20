/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*# Determine if we trust our partner. If we trust them, we can be more liberal
 *# with error checking.
 #*/
/*- set trust_partner = configuration[me.to_instance.name].get('trusted') == '"true"' -*/

/*- set base = '((void*)&seL4_GetIPCBuffer()->msg[0])' -*/
/*- set buffer = configuration[me.from_instance.name].get('%s_buffer' % me.from_interface.name) -*/
/*- if buffer is not none -*/
    extern void * /*? buffer ?*/;
/*- endif -*/
/*- set userspace_ipc = buffer is not none -*/
/*- set base = base if buffer is none else buffer -*/

/*- include 'rpc-connector-common-from.c' -*/
