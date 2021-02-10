/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <camkes/dataport.h>
#include <stddef.h>
#include <stdint.h>
#include <platsupport/io.h>
#include <utils/util.h>
#include <sel4/sel4.h>
/*? macros.show_includes(me.instance.type.includes) ?*/

/*- set index = me.parent.from_ends.index(me) -*/

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
/*- set page_size = macros.get_page_size(size, options.architecture) -*/
/*- if page_size == 0 -*/
  /*? raise(TemplateError('Setting %s.%s_size does not meet minimum size requirements. %d must be at least %d and %d aligned' % (me.parent.to_instance.name, me.parent.to_interface.name, size, 4096, 4096))) ?*/
/*- endif -*/
/*- set page_size_bits = int(math.log(page_size, 2)) -*/

/*- set cached = configuration[me.parent.to_instance.name].get('%s_hardware_cached' % me.parent.to_interface.name, False) -*/


/*- set dataport_symbol_name = "from_%d_%s_data" % (index, me.interface.name) -*/
struct {
    char content[ROUND_UP_UNSAFE(/*? macros.dataport_size(me.interface.type) ?*/,
        SIZE_BITS_TO_BYTES(/*? page_size_bits ?*/))];
} /*? dataport_symbol_name ?*/
        ALIGN(/*? page_size ?*/)
        SECTION("align_/*? page_size_bits ?*/bit")
        VISIBLE
        USED;
/*- set frame_caps = [] -*/
/*? register_shared_variable('%s_data' % me.parent.name, dataport_symbol_name, size, frame_size=page_size, perm='RW', paddr=paddr, cached=cached, with_mapping_caps=frame_caps) ?*/


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


/*# Check if we have reserved enough virtual memory for the MMIO. #*/
static_assert(/*? macros.dataport_size(me.interface.type) ?*/ == /*? size ?*/, "Data type mismatch!");


void * /*? me.interface.name ?*/_translate_paddr(
        uintptr_t paddr, size_t size) {
    if (paddr >= /*? paddr ?*/ && (paddr + size) <= /*? paddr + size ?*/) {
        return (void*)/*? me.interface.name ?*/ + (paddr - /*? paddr ?*/);
    }
    return NULL;
}

/*- for cap in frame_caps -*/
__attribute__((used)) __attribute__((section("_dataport_frames")))
dataport_frame_t /*? me.interface.name ?*//*? loop.index0 ?*/ = {
    .paddr = /*? paddr + loop.index0 * page_size ?*/,
    .cap = /*? cap ?*/,
    .size = /*? page_size ?*/,
    .vaddr = (uintptr_t)&(/*? dataport_symbol_name ?*/.content[/*? loop.index0 * page_size ?*/]),
};
/*- endfor -*/

/*# We only pull frame_caps from the stash. This is because only one caller of register_shared_variable
    should pass a frames parameter. By not stashing the frame_objs we ensure that only the original
    creator passed the frames, and everyone else will still have a None here #*/

/* Flush data corresponding to the dataport-relative address range from the CPU cache */
int /*? me.interface.name ?*/_flush_cache(size_t start_offset UNUSED, size_t size UNUSED, dma_cache_op_t cache_op UNUSED) {
    return camkes_dataport_flush_cache(start_offset, size, (uintptr_t) &/*? dataport_symbol_name ?*/.content,
                                       /*? size ?*/, cache_op);
}
