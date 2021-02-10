/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/dataport.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/

/*- if me in me.parent.from_ends -*/
  /*- set index = me.parent.from_ends.index(me) -*/
  /*- set end = 'from' -*/
/*- elif me in me.parent.to_ends -*/
  /*- set index = me.parent.to_ends.index(me) -*/
  /*- set end = 'to' -*/
/*- endif -*/

/*- set dataport_symbol_name = "%s_%d_%s_data" % (end, index, me.interface.name) -*/
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
    (/*? macros.dataport_type(me.interface.type) ?*/ *) & /*? end ?*/_/*? index ?*/_/*? me.interface.name ?*/_data;

/*- set id = composition.connections.index(me.parent) -*/

int /*? me.interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    if ((uintptr_t)ptr < (uintptr_t)/*? me.interface.name ?*/ ||
            (uintptr_t)ptr >= (uintptr_t)/*? me.interface.name ?*/ + /*? macros.dataport_size(me.interface.type) ?*/) {
        return -1;
    }
    p->id = /*? id ?*/;
    p->offset = (off_t)((uintptr_t)ptr - (uintptr_t)/*? me.interface.name ?*/);
    return 0;
}

void * /*? me.interface.name ?*/_unwrap_ptr(dataport_ptr_t *p) {
    if (p->id == /*? id ?*/) {
        return (void*)((uintptr_t)/*? me.interface.name ?*/ + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}
