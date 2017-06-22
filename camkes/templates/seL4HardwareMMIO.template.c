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

#include <assert.h>
#include <camkes/dataport.h>
#include <stddef.h>
#include <stdint.h>
#include <utils/util.h>
/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set index = me.parent.from_ends.index(me) -*/

/*- set dataport_symbol_name = "from_%d_%s_data" % (index, me.interface.name) -*/
#define MMIO_ALIGN (1 << 12)
struct {
    char content[ROUND_UP_UNSAFE(/*? macros.dataport_size(me.interface.type) ?*/,
        PAGE_SIZE_4K)];
} /*? dataport_symbol_name ?*/
        ALIGN(MMIO_ALIGN)
        __attribute__((section("ignore_from_/*? index ?*/_/*? me.interface.name ?*/")))
        VISIBLE;

/*- do keep_symbol(dataport_symbol_name) -*/

volatile /*? macros.dataport_type(me.interface.type) ?*/ * /*? me.interface.name ?*/ =
    (volatile /*? macros.dataport_type(me.interface.type) ?*/ *) & /*? dataport_symbol_name ?*/;

/*- set id = composition.connections.index(me.parent) -*/

int /*? me.interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    /*- set offset = c_symbol('offset') -*/
    off_t /*? offset ?*/ = (off_t)((uintptr_t)ptr - (uintptr_t)/*? me.interface.name ?*/);
    if (/*? offset ?*/ < /*? macros.dataport_size(me.interface.type) ?*/) {
        p->id = /*? id ?*/;
        p->offset = /*? offset ?*/;
        return 0;
    } else {
        return -1;
    }
}

void * /*? me.interface.name ?*/_unwrap_ptr(dataport_ptr_t *p) {
    if (p->id == /*? id ?*/) {
        return (void*)((uintptr_t)/*? me.interface.name ?*/ + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}

/*- set paddr = configuration[me.parent.to_instance.name].get('%s_paddr' % me.parent.to_interface.name) -*/
/*- if paddr is none -*/
  /*? raise(TemplateError('Setting %s.%s_paddr that should specify the physical address of an MMIO device is not set' % (me.parent.to_instance.name, me.parent.to_interface.name))) ?*/
/*- endif -*/
/*- if not isinstance(paddr, numbers.Integral) or paddr < 0 -*/
  /*? raise(TemplateError('Setting %s.%s_paddr that should specify the physical address of an MMIO device does not appear to be a valid address' % (me.parent.to_instance.name, me.parent.to_interface.name))) ?*/
/*- endif -*/

/*- set size = configuration[me.parent.to_instance.name].get('%s_size' % me.parent.to_interface.name) -*/
/*- if size is none -*/
  /*? raise(TemplateError('Setting %s.%s_size that should specify the size of an MMIO device is not set' % (me.parent.to_instance.name, me.parent.to_interface.name))) ?*/
/*- endif -*/
/*- if not isinstance(size, numbers.Integral) or size <= 0 -*/
  /*? raise(TemplateError('Setting %s.%s_size that should specify the size of an MMIO device does not appear to be a valid size' % (me.parent.to_instance.name, me.parent.to_interface.name))) ?*/
/*- endif -*/

/*# Check if we have reserved enough virtual memory for the MMIO. #*/
static_assert(/*? macros.dataport_size(me.interface.type) ?*/ == /*? size ?*/, "Data type mismatch!");

void * /*? me.interface.name ?*/_translate_paddr(
        uintptr_t paddr, size_t size) {
    if (paddr == /*? paddr ?*/ && size == /*? size ?*/) {
        return (void*)/*? me.interface.name ?*/;
    }
    return NULL;
}

/*- do register_shared_variable('%s_data' % me.parent.name, 'from_%d_%s_data' % (index, me.interface.name), 'RW', paddr) -*/
