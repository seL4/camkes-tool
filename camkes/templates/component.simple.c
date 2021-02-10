/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* This template is meant to be used for components that are themselves dynamic systems
 * and need to create seL4 objects dynamically at run time. This is *not* the standard
 * use case for CAmkES and should only be used as a last resort if what you want is
 * really not possible any other way. This template is also highly experimental and
 * unsupported / undocumented */

/*- if configuration[me.name].get('simple') -*/

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <assert.h>
#include <sel4/types.h>
#include <sel4/sel4.h>
#include <sel4utils/mapping.h>
#include <stddef.h>
#include <stdint.h>
#include <camkes/error.h>
#include <camkes/tls.h>
#include <vka/kobject_t.h>

#include <simple/simple.h>

/*- set self_cnode = alloc_cap('cnode', my_cnode, write=true) -*/
/*- set self_pd = alloc_cap('my_pd_cap', my_pd, write=true) -*/

/*- if options.realtime -*/
/*- if 'sched_ctrl' in configuration[me.name].keys() -*/
    /*- set sched_control = alloc('sched_control', type=seL4_SchedControl, core=configuration[me.name].get('sched_ctrl')) -*/
/*- endif -*/
/*- endif -*/

/*- set extrabi_list = [] -*/
/*- for value in configuration[me.name].get('simple_extra_bootinfo',[]) -*/
    /*- set name = value.strip('"') -*/
    /*- set symbol = 'extra_bootinfo_frame_%d' % loop.index0 -*/
    struct {
        char content[PAGE_SIZE_4K];
    } /*? symbol ?*/ ALIGN(PAGE_SIZE_4K) SECTION("align_12bit");
    /*- do register_fill_frame(symbol, 'CDL_FrameFill_BootInfo %s' % name, 4096) -*/
    /*- do extrabi_list.append((name, symbol)) -*/
/*- endfor -*/

/*# Find any untyped pools #*/
/*- set untyped_obj_list = [] -*/
/*- for attribute, value in configuration[me.name].items() -*/
    /*- set r = re.match('simple_untyped(\\d+)_pool$', attribute) -*/
    /*- if r is not none -*/
        /*- set bits = int(r.group(1)) -*/
        /*- for i in six.moves.range(value) -*/
            /*- if not macros.min_untyped_size(options.architecture) <= bits <= macros.max_untyped_size(options.architecture) -*/
                /*? raise(TemplateError('illegal untyped size')) ?*/
            /*- endif -*/
            /*- set untyped = alloc('simple_untyped_%d_pool_%d' % (bits, i), seL4_UntypedObject, size_bits=bits) -*/
            /*- do untyped_obj_list.append((untyped, bits)) -*/
        /*- endfor -*/
    /*- endif -*/
/*- endfor -*/

/*# Find any configuration IO ports #*/
/*- set ioports = [] -*/
/*- set ioport_list = configuration[me.name].get('ioports') -*/
/*- if ioport_list is not none -*/
    /*- set ioport_list = ioport_list.strip('"').split(',') -*/
    /*- for ioport in ioport_list -*/
        /*- set start, end = ioport.split(':') -*/
        /*- set start = int(start, 0) -*/
        /*- set end = int(end, 0) -*/
        /*- set ioport_cap = alloc("ioport%d_%d" % (start, end), seL4_IA32_IOPort, start_port=start, end_port=end + 1) -*/
        /*- do ioports.append( (ioport_cap, start, end) ) -*/
    /*- endfor -*/
/*- endif -*/

/*# Find any configuration mmio regions #*/
/*- set mmio_regions = [] -*/
/*- set mmio_region_list = configuration[me.name].get('mmios') -*/
/*- if mmio_region_list is not none -*/
    /*- for mmio_region in mmio_region_list -*/
        /*- set paddr, size, bits = mmio_region.split(':') -*/
        /*- do mmio_regions.append( (int(paddr, 0), int(size, 0),int(bits, 0)) ) -*/
    /*- endfor -*/
/*- endif -*/

/*# Allocates capabilities for all the MMIO regions #*/
/*- set mmio_caps_len = [] -*/
/*# Map size to seL4 object. The arm HYP kernel has different sizes for
    some objects. But as they do not overlap we can just include both
    and rely on the component author to get it right #*/
/*- set bits_to_frame_type = { 12:seL4_FrameObject, 20:seL4_ARM_SectionObject, 21:seL4_ARM_SectionObject } -*/
/*- do mmio_caps_len.append(0) -*/
/*- for paddr, size, bits in mmio_regions -*/
    /*- set mmio_key = '0x%x_0x%x' % (paddr, size) -*/
    static seL4_CPtr mmio_cap_lookup_/*? mmio_key ?*/[] = {
    /*- for frame_offset in six.moves.range(0, size, 2 ** bits) -*/
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
/*- set ut_mmio_list = configuration[me.name].get('untyped_mmios') -*/
/*- if ut_mmio_list is not none -*/
    /*- for ut_mmio in ut_mmio_list -*/
        /*- set paddr, size_bits = ut_mmio.split(':') -*/
        /*- set paddr = int(paddr, 0) -*/
        /*- set size_bits = int(size_bits, 0) -*/
        /*- set cap = alloc('untyped_cap_0x%x' % paddr, seL4_UntypedObject, paddr = paddr, size_bits = size_bits) -*/
        /*- do untyped_mmio.append( (paddr, size_bits, cap) ) -*/
    /*- endfor -*/
/*- endif -*/

/*# Allocate any IOSpace caps #*/
/*- set iospaces = [] -*/
/*- set iospace_list = configuration[me.name].get('iospaces') -*/
/*- if iospace_list is not none -*/
    /*- set iospace_list = iospace_list.strip('"').split(',') -*/
    /*- for iospace in iospace_list -*/
        /*- set domain, bus, dev, fun = iospace.split(':') -*/
        /*- set domain = int(domain, 0) -*/
        /*- set bus = int(bus, 0) -*/
        /*- set dev = int(dev, 0) -*/
        /*- set fun = int(fun, 0) -*/
        /*- set pciid = bus * 256 + dev * 8 + fun -*/
        /*- set devid = domain * 65536 + pciid -*/
        /*- set iospace_cap = alloc('iospace_%d' % devid, seL4_IA32_IOSpace, domainID=domain, bus=bus, dev=dev, fun=fun) -*/
        /*- do iospaces.append((devid, iospace_cap)) -*/
    /*- endfor -*/
/*- endif -*/

/*# Allocate any SMMU caps #*/
/*- for smmu in configuration[me.name].get('smmu',[]) -*/
    /*- set smmu_cap = alloc('smmu_%d' % smmu, seL4_ARM_IOSpace, iospace=smmu) -*/
    /*- do iospaces.append((smmu, smmu_cap)) -*/
/*- endfor -*/

/*# Allocate asid pool cap #*/
/*- if configuration and configuration[me.name].get('asid_pool') -*/
    /*- set asidpool = alloc('asid_pool', seL4_ASID_Pool) -*/
/*- endif -*/

/*- set irq_notification_object = alloc_obj('irq_notification_obj', seL4_NotificationObject) -*/
/*- set irq_notification = alloc_cap('irq_notification_obj', irq_notification_object, read=True) -*/
/*- set irqs = [] -*/
/*- set irq_list = configuration[me.name].get('irqs') -*/
/*- if irq_list is not none -*/
    /*- for irq in irq_list -*/
        /*- set irq_cap = alloc('irq_%d' % irq, seL4_IRQHandler, number=irq, notification=my_cnode[irq_notification]) -*/
        /*- do irqs.append( (irq, irq_cap) ) -*/
    /*- endfor -*/
/*- endif -*/

/*# No cap allocation from here on! We assume all caps exist so we can guess our cnode size from the
 * holding slot #*/
/*- set holding_slot = alloc_cap('temporary_simple_slot', None) -*/

/*# We need to have a known cspace size to instantiate a simple. This logic is
    more complicated than it strictly needs to be since in practice camkes will
    always have an 'auto' size, but it does not hurt to be general here #*/
/*- if cap_space.cnode.size_bits == 'auto' -*/
    /*- set size_bits = configuration[me.name].get('cnode_size_bits') -*/
    /*- if size_bits is not none -*/
        /*- set cnodesize = size_bits -*/
    /*- else -*/
        /*# We will determine the size at run time #*/
        /*- set cnodesize = None -*/
    /*- endif -*/
/*- else -*/
    /*- set cnodesize = cap_space.cnode.size_bits -*/
/*- endif -*/

/* Static declaration for our cap information. We will populate this when we make
 * the simple */
typedef struct camkes_untyped {
    seL4_CPtr cptr;
    uintptr_t paddr;
    int size_bits;
    int device;
} camkes_untyped_t;
typedef struct camkes_simple_data {
/*- if cnodesize is none -*/
    int cnodesizebits;
/*- endif -*/
    camkes_untyped_t untyped[/*? len(untyped_obj_list) + len(untyped_mmio) ?*/];
    seL4_CPtr inittcb;
    seL4_CPtr initsc;
} camkes_simple_data_t;
static camkes_simple_data_t simple_data;
static bool camkes_simple_init = false;

static int simple_camkes_untyped_count(void *data) {
    return /*? len(untyped_obj_list) + len(untyped_mmio) ?*/;
}

static int simple_camkes_cap_count(void *data) {
    /*# untypeds + mmio +ioports + cnode + pd + iospaces + holding #*/
    return /*? len(untyped_obj_list) + mmio_caps_len[0] + len(ioports) + len(iospaces) + len(untyped_mmio) + 3 ?*/;
}

static seL4_CPtr simple_camkes_nth_untyped(void *data, int n, size_t *size_bits, uintptr_t *paddr, bool *device) {
    camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
    if (size_bits) {
        *size_bits = (size_t)camkes->untyped[n].size_bits;
    }
    if (paddr) {
        *paddr = camkes->untyped[n].paddr;
    }
    if (device) {
        *device = camkes->untyped[n].device;
    }
    return camkes->untyped[n].cptr;
}

static seL4_Error simple_camkes_get_frame_cap(void *data, void *paddr, int size_bits, cspacepath_t *path) {
    /*- if len(mmio_regions) > 0 -*/
        /*- for paddr, size, bits in mmio_regions -*/
            /*- set mmio_key = '0x%x_0x%x' % (paddr, size) -*/
            if ((uintptr_t)paddr >= (uintptr_t)/*? paddr ?*/ && (uintptr_t)paddr < (uintptr_t)/*? paddr ?*/ + (uintptr_t)/*? size ?*/ && size_bits == /*? bits ?*/) {
                return seL4_CNode_Copy(path->root, path->capPtr, path->capDepth, /*? self_cnode ?*/, mmio_cap_lookup_/*? mmio_key ?*/[((uintptr_t)paddr - (uintptr_t)/*? paddr ?*/) >> /*? bits ?*/], CONFIG_WORD_SIZE, seL4_AllRights);
            }
        /*- endfor -*/
    /*- endif -*/
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
        /*- set mmio_key = '0x%x_0x%x' % (paddr, size) -*/
        /*- set mmio_range_len = len(list(six.moves.range(0, size, 2 ** bits))) -*/
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
    /*- if options.realtime -*/
    case seL4_CapInitThreadSC:
        return camkes->initsc;
    /*- endif -*/
    default:
        assert(!"Unsupported init_cap requested");
    }
    return 0;
}

static uint8_t simple_camkes_cnode_size(void *data) {
    /*- if cnodesize is none -*/
        camkes_simple_data_t *camkes = (camkes_simple_data_t *)data;
        return camkes->cnodesizebits;
    /*- else -*/
        return /*? cnodesize ?*/;
    /*- endif -*/
}

static seL4_Error simple_camkes_get_IOPort_cap(void *data, uint16_t start_port, uint16_t end_port, seL4_Word root, seL4_Word dest, seL4_Word depth) {
    assert(start_port <= end_port);
    seL4_CPtr cap = seL4_CapNull;
    /*- for cap, start, end in ioports -*/
        if (start_port >= /*? start ?*/ && end_port <= /*? end ?*/) {
            cap = /*? cap ?*/;
        }
    /*- endfor -*/
    if (cap == seL4_CapNull) {
        ERR(camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "unable to find IO port cap",
            }), ({
                return seL4_FailedLookup;
            }));
        return seL4_FailedLookup;
    }
    return seL4_CNode_Copy(root, dest, depth, /*? self_cnode ?*/, cap, CONFIG_WORD_SIZE, seL4_AllRights);
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
        return seL4_CNode_Copy(path->root, path->capPtr, path->capDepth, /*? self_cnode ?*/, cap, CONFIG_WORD_SIZE, seL4_AllRights);
    /*- else -*/
        return seL4_FailedLookup;
    /*- endif -*/
}
#endif

#ifdef CONFIG_TK1_SMMU
static seL4_Error simple_camkes_get_iospace_cap_count(void *data, int *count) {
    if (count) {
        *count = /*? len(iospaces) ?*/;
    }
    return seL4_NoError;
}

static seL4_CPtr simple_camkes_get_iospace_nth_cap(void *data, int n) {
    /*- if len(iospaces) > 0 -*/
        switch (n) {
        /*- for smmu, cap in iospaces -*/
            case /*? loop.index0 ?*/:
                return /*? cap ?*/;
        /*- endfor -*/
        default:
            return 0;
        }
    /*- else -*/
        return 0;
    /*- endif -*/
}
#endif

static void simple_camkes_print(void *data) {
    printf("camkes is too cool to print out simple information\n");
}

static seL4_Error simple_camkes_set_ASID(void *data, seL4_CPtr vspace) {
    /*- if configuration[me.name].get('asid_pool') -*/
#ifdef CONFIG_ARCH_X86
        return seL4_X86_ASIDPool_Assign(/*? asidpool ?*/, vspace);
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
                return seL4_CNode_Copy(cnode, index, depth, /*? self_cnode ?*/, /*? cap ?*/, CONFIG_WORD_SIZE, seL4_AllRights);
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
    type = seL4_ARCH_4KPage;
#ifdef CONFIG_KERNEL_STABLE
    error = seL4_Untyped_RetypeAtOffset(untyped, type, 0, 12, /*? self_cnode ?*/, 0, 0, /*? holding_slot ?*/, 1);
#else
    error = seL4_Untyped_Retype(untyped, type, 12, /*? self_cnode ?*/, 0, 0, /*? holding_slot ?*/, 1);
#endif
    ERR_IF(error != seL4_NoError, camkes_error, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.name ?*/",
            .description = "failed to retype an untyped while trying to determine its physical address",
            .syscall = UntypedRetype,
            .error = error,
        }), ({
            return (uintptr_t)NULL;
        }));
    seL4_ARCH_Page_GetAddress_t res = seL4_ARCH_Page_GetAddress(/*? holding_slot ?*/);
    ret = res.paddr;
    ERR_IF(ret == 0, camkes_error, ((camkes_error_t){
            .type = CE_SYSCALL_FAILED,
            .instance = "/*? me.name ?*/",
            .description = "failed to retrieve the physical address of a temporary frame",
            .syscall = ARCHPageGetAddress,
            .error = res.error,
        }), ({
            return (uintptr_t)NULL;
        }));
    seL4_CNode_Delete(/*? self_cnode ?*/, /*? holding_slot ?*/, CONFIG_WORD_SIZE);
    return ret;
}

static void camkes_make_arch_simple(arch_simple_t *simple) {
    simple->irq = &simple_camkes_get_irq;
#ifdef CONFIG_IOMMU
    simple->iospace = &simple_camkes_get_iospace;
#endif
/*- if options.architecture in ('ia32', 'x86_64') -*/
    simple->IOPort_cap = &simple_camkes_get_IOPort_cap;
/*- endif -*/
}

static ssize_t camkes_get_extended_bootinfo(void *data, seL4_Word type, void *dest, ssize_t max_len) {
    seL4_BootInfoHeader *mapping = NULL;
    /*- for name, symbol in extrabi_list -*/
    if (type == /*? name ?*/) {
        mapping = (seL4_BootInfoHeader*)&/*? symbol ?*/.content[0];
    }
    /*- endfor -*/
    if (mapping && mapping->len != -1) {
        ssize_t len = MIN(mapping->len, max_len);
        memcpy(dest, mapping, len);
        return len;
    }
    return -1;
}

static UNUSED seL4_CPtr camkes_simple_sched_ctrl(void *data, int core) {
    /*- if options.realtime -*/
    /*- if 'sched_ctrl' in configuration[me.name].keys() -*/
    if (core == /*? configuration[me.name].get('sched_ctrl') ?*/) {
        return /*? sched_control ?*/;
    }
    /*- endif -*/
    /*- endif -*/
    return seL4_CapNull;
}

static int camkes_simple_core_count(void *data) {
    return CONFIG_MAX_NUM_NODES;
}

void camkes_make_simple(simple_t *simple) {
    if (!camkes_simple_init) {
        /*- if cnodesize is none -*/
            /* Guess the size of our cnode by rounding */
            /*# If there is no size specified in the configuration then we assume the cnode
                will be as small as possible to hold all the capabilities that are currently
                defined #*/
            simple_data.cnodesizebits = CONFIG_WORD_SIZE - __builtin_clz(/*? holding_slot ?*/) + 1;
        /*- endif -*/
        /*# Find untyped physical addresses. We only care if the untyped is at least a page size #*/
        /*- for u in untyped_obj_list -*/
            /*- if u[1] >= 12 -*/
                simple_data.untyped[/*? loop.index0 ?*/] = (camkes_untyped_t) {.cptr = /*? u[0] ?*/, .paddr = make_frame_get_paddr(/*? u[0] ?*/), .size_bits = /*? u[1] ?*/, .device = false};
            /*- endif -*/
        /*- endfor -*/
        /*- for paddr, size_bits, cap in untyped_mmio -*/
            simple_data.untyped[/*? loop.index0 + len(untyped_obj_list) ?*/] = (camkes_untyped_t){.cptr = /*? cap ?*/, .paddr = /*? paddr ?*/, .size_bits = /*? size_bits ?*/, .device = true};
        /*- endfor -*/
        camkes_simple_init = true;
    }
    /* Assume we are called from init */
    simple_data.inittcb = camkes_get_tls()->tcb_cap;
    simple_data.initsc = camkes_get_tls()->sc_cap;
    simple->data = &simple_data;
    simple->frame_info = /*&simple_camkes_get_frame_info*/NULL;
    simple->frame_cap = &simple_camkes_get_frame_cap;
    simple->frame_mapping = /*&simple_camkes_get_frame_mapping*/NULL;
    simple->ASID_assign = &simple_camkes_set_ASID;
    simple->cap_count = &simple_camkes_cap_count;
    simple->nth_cap = &simple_camkes_nth_cap;
    simple->init_cap = &simple_camkes_init_cap;
    simple->cnode_size = &simple_camkes_cnode_size;
    simple->untyped_count = &simple_camkes_untyped_count;
    simple->nth_untyped = &simple_camkes_nth_untyped;
    simple->userimage_count = /*&simple_camkes_userimage_count*/NULL;
    simple->nth_userimage = /*&simple_camkes_nth_userimage*/NULL;
    simple->extended_bootinfo = &camkes_get_extended_bootinfo;
#ifdef CONFIG_KERNEL_MCS
    simple->sched_ctrl = &camkes_simple_sched_ctrl;
    simple->core_count = &camkes_simple_core_count;
#endif
#ifdef CONFIG_TK1_SMMU
    simple->arch_simple.iospace_cap_count = simple_camkes_get_iospace_cap_count;
    simple->arch_simple.iospace_get_nth_cap = simple_camkes_get_iospace_nth_cap;
#endif
    simple->print = &simple_camkes_print;

    camkes_make_arch_simple(&simple->arch_simple);
}

/*- endif -*/
