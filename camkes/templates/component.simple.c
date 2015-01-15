/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/* This template is meant to be used for components that are themselves dynamic systems
 * and need to create seL4 objects dynamically at run time. This is *not* the standard
 * use case for CAmkES and should only be used as a last resort if what you want is
 * really not possible any other way. This template is also highly experimental and
 * unsupported / undocumented */

/*- if configuration and filter(lambda('x: x.instance == \'%s\' and x.attribute == \'simple\' and x.value == \'true\'' % (me.name)),  configuration.settings) -*/

#include <autoconf.h>
#include <assert.h>
#include <sel4/types.h>
#include <sel4/sel4.h>
#include <camkes/tls.h>
#include <vka/kobject_t.h>

#include <simple/simple.h>

/*- set self_cnode = alloc_cap('cnode', my_cnode, write=true) -*/
/*- set self_pd = alloc_cap('my_pd_cap', my_pd, write=true) -*/

/*# Find any untyped pools #*/
/*- set untyped_obj_list = [] -*/
/*- for s in configuration.settings -*/
    /*- if s.instance == me.name -*/
        /*- set r = re.match('simple_untyped([0-9]+)_pool', s.attribute) -*/
        /*- if r -*/
            /*- set bits = r.group(1) -*/
            /*- set count = s.value -*/
            /*- for i in range(count) -*/
                /*- if int(bits) > 28 or int(bits) < 4 -*/
                    /*? raise(Exception('illegal untyped size')) ?*/
                /*- endif -*/
                /*- set untyped = alloc('simple_untyped_%s_pool_%d' % (bits, i), seL4_UntypedObject, size_bits=int(bits), read=True, write=True) -*/
                /*- do untyped_obj_list.append((untyped, bits)) -*/
            /*- endfor -*/
        /*- endif -*/
    /*- endif -*/
/*- endfor -*/

/*# Find any configuration IO ports #*/
/*- set ioports = [] -*/
/*- for i in configuration.settings -*/
    /*- if i.instance == me.name and i.attribute == 'ioport' -*/
        /*- set start, end = i.value.strip('"').split(':') -*/
        /*- set start = int(start, 16) -*/
        /*- set end = int(end, 16) -*/
        /*- set ioport_cap = alloc("ioport%d_%d" % (start, end), seL4_IA32_IOPort) -*/
        /*- do cap_space.cnode[ioport_cap].set_ports(range(start, end +1)) -*/
        /*- do ioports.append( (ioport_cap, start, end) ) -*/
    /*- endif -*/
/*- endfor -*/

/*# Find any configuration mmio regions #*/
/*- set mmio_regions = [] -*/
/*- for i in configuration.settings -*/
    /*- if i.instance == me.name and i.attribute == 'mmio' -*/
        /*- set paddr, size, bits = i.value.strip('"').split(':') -*/
        /*- do mmio_regions.append( (int(paddr, 16), int(size, 16),int(bits, 10)) ) -*/
    /*- endif -*/
/*- endfor -*/

/*# Allocates capabilities for all the MMIO regions #*/
/*- set mmio_caps_len = [] -*/
/*# Map size to seL4 object. The arm HYP kernel has different sizees for
    some objects. But as they do not overlap we can just include both
    and rely on the component author to get it right #*/
/*- set bits_to_frame_type = { 12:seL4_FrameObject, 20:seL4_ARM_SectionObject, 21:seL4_ARM_SectionObject } -*/
/*- do mmio_caps_len.append(0) -*/
/*- for paddr, size, bits in mmio_regions -*/
    /*- set mmio_key = '%d%d' % (paddr, size) -*/
    static seL4_CPtr mmio_cap_lookup_/*? mmio_key ?*/[] = {
    /*- for frame_offset in range(0, size, 2 ** bits) -*/
        /*- set frames = paddr + frame_offset -*/
        /*- set temp_object=alloc_obj('mmio_frame_%d' % frames, bits_to_frame_type[bits], paddr=frames) -*/
        /*- set temp_cap = alloc_cap('mmio_frame_%d' % frames, temp_object, read=true, write=true) -*/
        /*? temp_cap ?*/,
        /*- do mmio_caps_len.append(mmio_caps_len.pop() + 1) -*/
    /*- endfor -*/
    };
/*- endfor -*/

/*# Find an allocate untyped MMIO capabilities #*/
/*- set untyped_mmio = [] -*/
/*- for i in configuration.settings -*/
    /*- if i.instance == me.name and i.attribute == 'untyped_mmio' -*/
        /*- set paddr, size_bits = i.value.strip('"').split(':') -*/
        /*- set paddr = int(paddr, 0) -*/
        /*- set size_bits = int(size_bits, 0) -*/
        /*- set cap = alloc('untyped_cap_%d' % paddr, seL4_UntypedObject, read=True, write=True, paddr = paddr, size_bits = size_bits) -*/
        /*- do untyped_mmio.append( (paddr, size_bits, cap) ) -*/
    /*- endif -*/
/*- endfor -*/

/*# Allocate any IOSpace caps #*/
/*- set iospaces = [] -*/
/*- for i in configuration.settings -*/
    /*- if i.instance == me.name and i.attribute == 'iospace' -*/
        /*- set domain, bus, dev, fun = i.value.strip('"').split(':') -*/
        /*- set domain = int(domain, 16) -*/
        /*- set bus = int(bus, 16) -*/
        /*- set dev = int(dev, 16) -*/
        /*- set fun = int(fun, 10) -*/
        /*- set pciid = bus * 256 + dev * 8 + fun -*/
        /*- set devid = domain * 65536 + pciid -*/
        /*- set iospace_cap = alloc('iospace_%d' % devid, seL4_IA32_IOSpace, domainID=domain, bus=bus, dev=dev, fun=fun) -*/
        /*- do iospaces.append((devid, iospace_cap)) -*/
        /*# do cap_space.cnode[iospace_cap].set_iospace( (domain, bus, dev, fun) ) #*/
    /*- endif -*/
/*- endfor -*/

/*# Allocate asid pool cap #*/
/*- if configuration and filter(lambda('x: x.instance == \'%s\' and x.attribute == \'asid_pool\' and x.value == \'true\'' % (me.name)),  configuration.settings) -*/
    /*- set asidpool = alloc('asid_pool', seL4_ASID_Pool) -*/
/*- endif -*/

/*- set irqaep_object = alloc_obj('irq_aep_obj', seL4_AsyncEndpointObject) -*/
/*- set irqaep = alloc_cap('irq_aep_obj', irqaep_object, read=True) -*/
/*- set irqs = [] -*/
/*- for i in configuration.settings -*/
    /*- if i.instance == me.name and i.attribute == 'irq' -*/
        /*- set irq = i.value.strip('"') -*/
        /*- set irq = int(irq, 10) -*/
        /*- set irq_cap = alloc('irq_%d' % irq, seL4_IRQControl, number=irq, aep=irqaep_object) -*/
        /*- do irqs.append( (irq, irq_cap) ) -*/
    /*- endif -*/
/*- endfor -*/

/*# No cap allocation from here on! We assume all caps exist so we can guess our cnode size from the
 * holding slot #*/
/*- set holding_slot = alloc_cap('temporary_simple_slot', None) -*/

/*# We need to have a known cspace size to instatiate a simple. This logic is
    more complicated than it strictly needs to be since in practice camkes will
    always have an 'auto' size, but it does not hurt to be general here #*/
/*- if cap_space.cnode.size_bits == 'auto' -*/
    /*- set size_bits = filter(lambda('x: x.instance == \'%s\' and x.attribute == \'cnode_size_bits\'' % (me.name)),  configuration.settings) -*/
    /*- if size_bits -*/
        /*- if len(size_bits) != 1 -*/
            /*? raise(Exception('Multiple cnode_size_bits specified. This makes no sense')) ?*/
        /*- endif -*/
        /*- do exec('cap_space.cnode.size_bits = %d' % (size_bits[0].value)) -*/
    /*- else -*/
        /*# We will determine the size at run time #*/
    /*- endif -*/
/*- else -*/
    simple_data.cnodesizebits = /*? cap_space.cnode.size_bits ?*/;
/*- endif -*/

/*- macro _cnodesize() -*/
    /*- if cap_space.cnode.size_bits == 'auto' -*/
        camkes->cnodesizebits
    /*- else -*/
        /*? cap_space.cnode.size_bits ?*/
    /*- endif -*/
/*- endmacro -*/

/*- macro _dataforsize() -*/
    /*- if cap_space.cnode.size_bits == 'auto' -*/
        camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
    /*- endif -*/
/*- endmacro -*/

/* Static declaration for our cap information. We will populate this when we make
 * the simple */
typedef struct camkes_untyped {
    seL4_CPtr cptr;
    uintptr_t paddr;
    int size_bits;
} camkes_untyped_t;
typedef struct camkes_simple_data {
/*- if cap_space.cnode.size_bits == 'auto' -*/
    int cnodesizebits;
/*- endif -*/
    camkes_untyped_t untyped[/*? len(untyped_obj_list) ?*/];
    seL4_CPtr inittcb;
} camkes_simple_data_t;
static camkes_simple_data_t simple_data;
static bool camkes_simple_init = false;

static int simple_camkes_untyped_count(void *data) {
    return /*? len(untyped_obj_list) ?*/;
}

static int simple_camkes_cap_count(void *data) {
    /*# untypeds + mmio +ioports + cnode + pd + iospaces + holding #*/
    return /*? len(untyped_obj_list) + mmio_caps_len[0] + len(ioports) + len(iospaces) + len(untyped_mmio) + 3 ?*/;
}

static seL4_CPtr simple_camkes_nth_untyped(void *data, int n, uint32_t *size_bits, uint32_t *paddr) {
    camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
    *size_bits = (uint32_t)camkes->untyped[n].size_bits;
    *paddr = (uint32_t)camkes->untyped[n].paddr;
    return camkes->untyped[n].cptr;
}

static seL4_Error simple_camkes_get_frame_cap(void *data, void *paddr, int size_bits, cspacepath_t *path) {
    /*- if len(mmio_regions) > 0 -*/
        /*- for paddr, size, bits in mmio_regions -*/
            /*- set mmio_key = '%d%d' % (paddr, size) -*/
            if ((uintptr_t)paddr >= (uintptr_t)/*? paddr ?*/ && (uintptr_t)paddr < (uintptr_t)/*? paddr ?*/ + (uintptr_t)/*? size ?*/ && size_bits == /*? bits ?*/) {
                return seL4_CNode_Copy(path->root, path->capPtr, path->capDepth, /*? self_cnode ?*/, mmio_cap_lookup_/*? mmio_key ?*/[((uintptr_t)paddr - (uintptr_t)/*? paddr ?*/) >> /*? bits ?*/], 32, seL4_AllRights);
            }
        /*- endfor -*/
    /*- endif -*/
#ifdef CONFIG_KERNEL_STABLE
    /*- if len(untyped_mmio) > 0 -*/
        /*- for paddr, size_bits, cap in untyped_mmio -*/
            if ((uintptr_t)paddr >= (uintptr_t)/*? paddr ?*/ && (uintptr_t)paddr + BIT(size_bits) <= (uintptr_t)/*? paddr ?*/ + (uintptr_t)/*? 2**size_bits ?*/) {
                return seL4_Untyped_RetypeAtOffset(/*? cap ?*/, kobject_get_type(KOBJECT_FRAME, size_bits), (seL4_Word)(paddr - /*? paddr ?*/), size_bits, path->root, path->dest, path->destDepth, path->offset, 1);
            }
        /*- endfor -*/
    /*- endif -*/
#endif
    return seL4_FailedLookup;
}

static seL4_CPtr simple_camkes_nth_cap(void *data, int n) {
    camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
    switch(n) {
    case 0:
        return /*? self_cnode ?*/;
    case 1:
        return /*? self_pd ?*/;
    /*- if len(untyped_obj_list) > 0 -*/
        case 2 ... /*? len(untyped_obj_list) + 1 ?*/:
            return camkes->untyped[n - 2].cptr;
    /*- endif -*/
    /*- set mmio_counter = [] -*/
    /*- do mmio_counter.append(0) -*/
    /*- for paddr, size, bits in mmio_regions -*/
        /*- set mmio_key = '%d%d' % (paddr, size) -*/
        /*- set mmio_range_len = len(range(0, size, 2 ** bits)) -*/
        case /*? 2 + len(untyped_obj_list) + mmio_counter[0] ?*/ ... /*? 2 + len(untyped_obj_list) + mmio_counter[0] + mmio_range_len - 1 ?*/:
            return mmio_cap_lookup_/*? mmio_key ?*/[n - /*? 2 + len(untyped_obj_list) + mmio_counter[0] ?*/];
        /*- do mmio_counter.append(mmio_counter.pop() + mmio_range_len) -*/
    /*- endfor -*/
    /*- for cap, start, end in ioports -*/
        case /*? 2 + len(untyped_obj_list) + mmio_caps_len[0] + loop.index0 ?*/:
            return /*? cap ?*/;
    /*- endfor -*/
    /*- for devid, cap in iospaces -*/
        case /*? 2 + len(untyped_obj_list) + mmio_caps_len[0] + len(ioports) + loop.index0 ?*/:
            return /*? cap ?*/;
    /*- endfor -*/
    /*- for paddr, size, cap in untyped_mmio -*/
        case /*? 2 + len(untyped_obj_list) + mmio_caps_len[0] + len(ioports) + len(iospaces) + loop.index0 ?*/:
            return /*? cap ?*/;
    /*- endfor -*/
    case /*? len(untyped_obj_list) + mmio_caps_len[0] + len(ioports) + len(iospaces) + len(untyped_mmio) + 2 ?*/:
        /*# The last cap we report is the magic holding slot we allocated.
         * technically this slot is probably free since we should have
         * deleted whatever was there. But this should also be the largest
         * cptr allocated, so is convenient to return it as the last cap #*/
        return /*? holding_slot ?*/;
    default:
        assert(!"Invalid cap requested");
    }
    return 0;
}

static seL4_CPtr simple_camkes_init_cap(void *data, seL4_CPtr cap) {
    camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
    switch(cap) {
    case seL4_CapInitThreadCNode:
        return /*? self_cnode ?*/;
    case seL4_CapInitThreadPD:
        return /*? self_pd ?*/;
    case seL4_CapInitThreadTCB:
        return camkes->inittcb;
    default:
        assert(!"Unsupported init_cap requested");
    }
    return 0;
}

static uint8_t simple_camkes_cnode_size(void *data) {
    /*- do _dataforsize() -*/
    return /*? _cnodesize() ?*/;
}

static seL4_CPtr simple_camkes_get_IOPort_cap(void *data, uint16_t start_port, uint16_t end_port) {
    assert(start_port <= end_port);
    /*- for cap, start, end in ioports -*/
        if (start_port >= /*? start ?*/ && end_port <= /*? end ?*/) {
            return /*? cap ?*/;
        }
    /*- endfor -*/
    assert(!"Unable to find IOPort cap");
    return 0;
}

#ifdef CONFIG_IOMMU
static seL4_Error simple_camkes_get_iospace(void *data, uint16_t domainID, uint16_t deviceID, cspacepath_t *path) {
    /*- if len(iospaces) > 0 -*/
        uint32_t devid = ((uint32_t)domainID << 16) | (uint32_t)deviceID;
        seL4_CPtr cap;
        switch(devid) {
        /*- for devid, cap in iospaces -*/
            case /*? devid ?*/:
                cap = /*? cap ?*/;
                break;
        /*- endfor -*/
            default:
                return seL4_FailedLookup;
        }
        return seL4_CNode_Copy(path->root, path->capPtr, path->capDepth, /*? self_cnode ?*/, cap, 32, seL4_AllRights);
    /*- else -*/
        return seL4_FailedLookup;
    /*- endif -*/
}
#endif

static void simple_camkes_print(void *data) {
    printf("camkes is too cool to print out simple information\n");
}

static seL4_Error simple_camkes_set_ASID(void *data, seL4_CPtr vspace) {
    /*- if configuration and filter(lambda('x: x.instance == \'%s\' and x.attribute == \'asid_pool\' and x.value == \'true\'' % (me.name)),  configuration.settings) -*/
#ifdef CONFIG_ARCH_IA32
        return seL4_IA32_ASIDPool_Assign(/*? asidpool ?*/, vspace);
#elif CONFIG_ARCH_ARM
        return seL4_ARM_ASIDPool_Assign(/*? asidpool ?*/, vspace);
#endif
    /*- else -*/
        return seL4_FailedLookup;
    /*- endif -*/
}

static seL4_Error simple_camkes_get_irq(void *data, int irq, seL4_CNode cnode, seL4_Word index, uint8_t depth) {
    /*- if len(irqs) > 0 -*/
        switch(irq) {
        /*- for irq,cap in irqs -*/
            case /*? irq ?*/:
                return seL4_CNode_Copy(cnode, index, depth, /*? self_cnode ?*/, /*? cap ?*/, 32, seL4_AllRights);
        /*- endfor -*/
            default:
                return seL4_FailedLookup;
        }
    /*- else -*/
        return seL4_FailedLookup;
    /*- endif -*/
}

static uintptr_t make_frame_get_paddr(seL4_CPtr untyped) {
    int type;
    int error;
    uintptr_t ret;
#ifdef CONFIG_ARCH_IA32
    type = seL4_IA32_4K;
#elif CONFIG_ARCH_ARM
    type = seL4_ARM_SmallPageObject;
#endif
#ifdef CONFIG_KERNEL_STABLE
    error = seL4_Untyped_RetypeAtOffset(untyped, type, 0, 12, /*? self_cnode ?*/, 0, 0, /*? holding_slot ?*/, 1);
#else
    error = seL4_Untyped_Retype(untyped, type, 12, /*? self_cnode ?*/, 0, 0, /*? holding_slot ?*/, 1);
#endif
    assert(error == seL4_NoError);
#ifdef CONFIG_ARCH_IA32
    ret = seL4_IA32_Page_GetAddress(/*? holding_slot ?*/).paddr;
#elif CONFIG_ARCH_ARM
    ret = seL4_ARM_Page_GetAddress(/*? holding_slot ?*/).paddr;
#endif
    assert(ret);
    seL4_CNode_Delete(/*? self_cnode ?*/, /*? holding_slot ?*/, 32);
    seL4_CNode_Recycle(/*? self_cnode ?*/, untyped, 32);
    return ret;
}

void camkes_make_simple(simple_t *simple) {
    if (!camkes_simple_init) {
        /*- if cap_space.cnode.size_bits == 'auto' -*/
            /* Guess the size of our cnode by rounding */
            /*# If there is no size specified in the configuration then we assume the cnode
                will be as small as possible to hold all the capabilities that are currently
                defined #*/
            simple_data.cnodesizebits = 32 - __builtin_clz(/*? holding_slot ?*/) + 1;
        /*- endif -*/
        /*# Find untyped physical addresses. We only care if the untyped is at least a page size #*/
        /*- for u in untyped_obj_list -*/
            /*- if u[1] >= 12 -*/
                simple_data.untyped[/*? loop.index0 ?*/] = (camkes_untyped_t) {.cptr = /*? u[0] ?*/, .paddr = make_frame_get_paddr(/*? u[0] ?*/), .size_bits = /*? u[1] ?*/ };
            /*- endif -*/
        /*- endfor -*/
        camkes_simple_init = true;
    }
    /* Assume we are called from init */
    simple_data.inittcb = camkes_get_tls()->tcb_cap;
    simple->data = &simple_data;
    simple->frame_info = /*&simple_camkes_get_frame_info*/NULL;
    simple->frame_cap = &simple_camkes_get_frame_cap;
    simple->frame_mapping = /*&simple_camkes_get_frame_mapping*/NULL;
    simple->irq = &simple_camkes_get_irq;
    simple->ASID_assign = &simple_camkes_set_ASID;
    simple->IOPort_cap = &simple_camkes_get_IOPort_cap;
    simple->cap_count = &simple_camkes_cap_count;
    simple->nth_cap = &simple_camkes_nth_cap;
    simple->init_cap = &simple_camkes_init_cap;
    simple->cnode_size = &simple_camkes_cnode_size;
    simple->untyped_count = &simple_camkes_untyped_count;
    simple->nth_untyped = &simple_camkes_nth_untyped;
    simple->userimage_count = /*&simple_camkes_userimage_count*/NULL;
    simple->nth_userimage = /*&simple_camkes_nth_userimage*/NULL;
#ifdef CONFIG_IOMMU
    simple->iospace = &simple_camkes_get_iospace;
#endif
    simple->print = &simple_camkes_print;
}

/*- endif -*/
