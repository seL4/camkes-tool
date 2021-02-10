/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/dataport.h>
#include <camkes/dma.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/


/*- set paddr = configuration[me.parent.name].get('paddr') -*/
/*- set size = configuration[me.parent.name].get('size', 4096) -*/

/*- set page_size = 4096 -*/
/*- set page_size_bits = int(math.log(page_size, 2)) -*/
/*- set cached = configuration[me.instance.name].get('%s_cached' % (me.interface.name), True) -*/
/*- set dataport_symbol_name = "%s_data" % (me.interface.name) -*/


/*? macros.shared_buffer_symbol(sym=dataport_symbol_name, shmem_size=size, page_size=page_size) ?*/
/*- set perm = macros.get_perm(configuration, me.instance.name, me.interface.name) -*/
/*- set frame_caps = [] -*/
/*? register_shared_variable('%s_data' % me.parent.name, dataport_symbol_name, size, frame_size=page_size, perm=perm, cached=cached, with_mapping_caps=frame_caps, paddr=paddr) ?*/

/*# Expose the frames backing the DMA pool #*/
/*- for cap in frame_caps -*/
    static dma_frame_t /*? me.interface.name ?*/_dma_/*? loop.index0 ?*/ = {
        .cap = /*? cap ?*/,
        .size = /*? page_size ?*/,
        .vaddr = (uintptr_t) &/*? dataport_symbol_name ?*/.content[/*? loop.index0 * page_size ?*/],
        .cached = /*?  int(cached) ?*/,
    };
/*- endfor -*/

static dma_frame_t */*? me.interface.name ?*/_dma_frames[] = {
    /*- for cap in frame_caps -*/
        &/*? me.interface ?*/_dma_/*? loop.index0 ?*/,
    /*- endfor -*/
};

static dma_pool_t /*? me.interface.name ?*/_dma_pool = {
    .start_vaddr = (uintptr_t) &/*? dataport_symbol_name ?*/.content[0],
    .end_vaddr = (uintptr_t) &/*? dataport_symbol_name ?*/.content[0] + /*? size ?*/ - 1,
    .frame_size = /*? page_size ?*/,
    .pool_size = /*? size ?*/,
    .num_frames = /*? len(frame_caps) ?*/,
    .dma_frames = /*? me.interface.name ?*/_dma_frames,
};
USED SECTION("_dma_pools")
dma_pool_t */*? me.interface.name ?*/_dma_pool_ptr = &/*? me.interface.name ?*/_dma_pool;

static void *dataport_addr = (void *)&/*? dataport_symbol_name ?*/;

/*- set id = composition.connections.index(me.parent) -*/

int /*? me.interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    if ((uintptr_t)ptr < (uintptr_t)dataport_addr ||
            (uintptr_t)ptr >= (uintptr_t)dataport_addr + /*? size ?*/) {
        return -1;
    }
    p->id = /*? id ?*/;
    p->offset = (off_t)((uintptr_t)ptr - (uintptr_t)dataport_addr);
    return 0;
}

void * /*? me.interface.name ?*/_unwrap_ptr(dataport_ptr_t *p) {
    if (p->id == /*? id ?*/) {
        return (void*)((uintptr_t)dataport_addr + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}


/*- if configuration[me.parent.name].get('controller') == str(me) -*/
static void __attribute__((constructor)) dma_init(void) {
    int res = camkes_dma_init(/*? dataport_symbol_name ?*/.content, /*? size ?*/, /*? page_size ?*/, /*? int(cached) ?*/);
    if (res) {
        ZF_LOGE("Invalid arguments given to camkes_dma_init in str(me)");
    }
}
/*- endif -*/
