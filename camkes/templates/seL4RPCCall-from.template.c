/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*- from 'rpc-connector.c' import establish_from_rpc, begin_send, perform_call, release_recv with context -*/

#include <camkes/dataport.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*? macros.show_includes(me.interface.type.includes) ?*/

/*- set connector = namespace() -*/

/*- set buffer = configuration[me.parent.name].get('buffer') -*/
/*- if buffer is none -*/
  /*? establish_from_rpc(connector) ?*/
/*- else -*/
  /*- if not isinstance(buffer, six.string_types) -*/
    /*? raise(TemplateError('invalid non-string setting for userspace buffer to back RPC connection', me.parent)) ?*/
  /*- endif -*/
  /*- if len(me.parent.from_ends) != 1 or len(me.parent.to_ends) != 1 -*/
    /*? raise(TemplateError('invalid use of userspace buffer to back RPC connection that is not 1-to-1', me.parent)) ?*/
  /*- endif -*/
  /*- set c = list(filter(lambda('x: x.name == \'%s\'' % buffer), composition.connections)) -*/
  /*- if len(c) == 0 -*/
    /*? raise(TemplateError('invalid setting to non-existent connection for userspace buffer to back RPC connection', me.parent)) ?*/
  /*- endif -*/
  /*- if len(c[0].from_ends) != 1 or len(c[0].to_ends) != 1 -*/
    /*? raise(TemplateError('invalid use of userspace buffer that is not 1-to-1 to back RPC connection', me.parent)) ?*/
  /*- endif -*/
  /*- if not isinstance(c[0].from_end.interface, camkes.ast.Dataport) -*/
    /*? raise(TemplateError('invalid use of non-dataport to back RPC connection', me.parent)) ?*/
  /*- endif -*/
  extern /*? macros.dataport_type(c[0].from_end.interface.type) ?*/ * /*? c[0].from_end.interface.name ?*/;
  /*# Conservatively count threads in this component to decide if we want lock access to the buffer #*/
  /*- set thread_count = (1 if me.instance.type.control else 0) + len(me.instance.type.provides) + len(me.instance.type.uses) + len(me.instance.type.emits) + len(me.instance.type.consumes) -*/
  /*- if thread_count > 1 -*/
    /*- set lock = True -*/
  /*- else -*/
    /*- set lock = False -*/
  /*- endif -*/
  /*? establish_from_rpc(connector, buffer=('((void*)%s)' % c[0].from_end.interface.name, macros.dataport_size(c[0].from_end.interface.type), lock)) ?*/
/*- endif -*/

/*- include 'rpc-connector-common-from.c' -*/
