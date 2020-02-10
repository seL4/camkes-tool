/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <camkes/dataport.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set index = me.parent.to_ends.index(me) -*/

/*- set dataport_symbol_name = "to_%d_%s_data" % (index, me.interface.name) -*/
/*- set type_size = macros.dataport_size(me.interface.type) -*/
/*- if type_size.startswith("sizeof") -*/
   /*- set size = configuration[me.parent.name].get('size', 4096) -*/
   /*- set page_size = macros.get_page_size(size, options.architecture) -*/
   /*- if page_size == 0 -*/
     /*? raise(TemplateError('Setting %s.size does not meet minimum size requirements. %d must be at least %d and %d aligned' % (me.parent.name, int(size), 4096, 4096))) ?*/
   /*- endif -*/
/*- else -*/
   /*- set size = type_size -*/
   /*- set page_size = macros.get_page_size(size, options.architecture) -*/
   /*- if page_size == 0 -*/
     /*? raise(TemplateError('Setting Buf(%d) does not meet minimum size requirements. %d must be at least %d and %d aligned' % (int(size), int(size), 4096, 4096))) ?*/
   /*- endif -*/
/*- endif -*/

/*- set shmem_symbol_size = "MAX_UNSAFE(%s, %s)" % (type_size, size) -*/
/*? macros.shared_buffer_symbol(sym=dataport_symbol_name, shmem_size=shmem_symbol_size, page_size=page_size) ?*/
/*- set perm = macros.get_perm(configuration, me.instance.name, me.interface.name) -*/
/*? register_shared_variable('%s_data' % me.parent.name, dataport_symbol_name, size, frame_size=page_size, perm=perm) ?*/

/*? macros.dataport_type(me.interface.type) ?*/ * /*? me.interface.name ?*/ =
    (/*? macros.dataport_type(me.interface.type) ?*/ *) & to_/*? index ?*/_/*? me.interface.name ?*/_data;

/*- include 'seL4SharedData-common.template.c' -*/
