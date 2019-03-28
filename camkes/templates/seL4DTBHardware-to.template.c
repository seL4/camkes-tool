/*
 * Copyright 2019, Data61
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
#include <stdbool.h>
#include <platsupport/io.h>
#include <utils/util.h>
#include <sel4/sel4.h>

/*# Grab the DTB object made from the previous stages of the parsing #*/
/*- set configuration_name = '%s.%s' % (me.instance.name, me.interface.name) -*/
/*- set dtb = configuration[configuration_name].get('dtb') -*/
/*- if dtb is none -*/
    /*# DTB path hasn't been passed, raise a fault #*/
    /*? raise(TemplateError('Missing DTB path, assign a DTB path to attribute %s.dtb.' % (me.interface.name))) ?*/
/*- endif -*/

/*# Check if we want interrupts #*/
/*- set generate_interrupts = configuration[configuration_name].get('generate_interrupts', none) -*/

/*# Extract the relevant fields from the DTB (regs, interrupts, etc) #*/
/*- set regs = dtb.get('reg') -*/
/*- set is_extended_interrupts = False -*/
/*- if generate_interrupts -*/
    /*- set interrupts = dtb.get('interrupts') -*/
    /*- if interrupts is none -*/
        /*- set interrupts = dtb.get('interrupts_extended') -*/
        /*- set is_extended_interrupts = True -*/
    /*- endif -*/
/*- else -*/
    /*- set interrupts = none -*/
/*- endif -*/

/*# ================ #*/
/*# Register section #*/
/*# ================ #*/

/*- if regs is not none -*/
    /*- if dtb.get('this_size_cells')[0] == 0 -*/
        /*? raise(TemplateError('This hardware device has a value of 0 for #size-cells, we do not support mapping in a block of 0 bytes')) ?*/
    /*- endif -*/

    /*- set num_address_cells = dtb.get('this_address_cells')[0] -*/
    /*- set num_size_cells = dtb.get('this_size_cells')[0] -*/

    /*- set reg_entry_size = num_address_cells + num_size_cells -*/
    /*- set num_regs = len(regs) // reg_entry_size -*/
    /*- for i in range(0, num_regs) -*/

        /*- set index = i -*/

        /*# Set a temporary namespace to bypass scoping #*/
        /*- set temp_ns = namespace(paddr=0, size=0) -*/
        /*- for j in range(0, num_address_cells) -*/ 
            /*# Extract the paddr and size, read back to front, the register address and size #*/
            /*# is written in big endian, __rshift__ because Jinja2 doesn't like '<<' #*/
            /*- set paddr_part = regs[i * reg_entry_size + j * (num_address_cells - 1)].__rshift__(j * 32) -*/ 
            /*- set temp_ns.paddr = temp_ns.paddr + paddr_part -*/
        /*- endfor -*/

        /*- for j in range(0, num_size_cells) -*/ 
            /*# Same idea as above #*/
            /*- set size_part = regs[i * reg_entry_size + j * (num_size_cells - 1) + num_address_cells].__rshift__(j * 32) -*/
            /*- set temp_ns.size = temp_ns.size + size_part -*/
        /*- endfor -*/

        /*- set paddr = temp_ns.paddr -*/
        /*- set size = temp_ns.size -*/

        /*# Get the next multiple of 4K that can fit the register #*/
        /*- set size = macros.next_page_multiple(size, options.architecture) -*/
        /*- set page_size = macros.get_page_size(size, options.architecture) -*/
        /*- set page_size_bits = int(math.log(page_size, 2)) -*/

        /*- set cached = configuration[configuration_name].get('hardware_cached', False) -*/

        /*- set dataport_symbol_name = "from_%d_%s_data" % (index, me.interface.name) -*/
        struct {
            char content[ROUND_UP_UNSAFE(/*? size ?*/,
                PAGE_SIZE_4K)];
        } /*? dataport_symbol_name ?*/
                ALIGN(/*? page_size ?*/)
                SECTION("align_/*? page_size_bits ?*/bit")
                VISIBLE
                USED;

        /*- set reg_interface_name = '%s_%d' % (me.interface.name, index) -*/

        /*? register_shared_variable('%s_data' % reg_interface_name, dataport_symbol_name, size, frame_size=page_size, perm='RW', paddr=paddr, cached=cached) ?*/

        /*# We need to copy all of the frame caps into our cspace for frame cache operations #*/
        /*- set frame_objs = get_shared_variable_backing_frames('%s_data' % reg_interface_name, size) -*/
        /*- set frame_caps = [] -*/
        /*- for (i, frame) in enumerate(frame_objs) -*/
            /*- set frame_cap = alloc_cap('%s_%d' % ('%s_data' % reg_interface_name, i), frame) -*/
            /*- do frame_caps.append(frame_cap) -*/
        /*- endfor -*/

        /*# Assign a name for this particular set of registers #*/
        volatile void * /*? reg_interface_name ?*/ =
            (volatile void *) & /*? dataport_symbol_name ?*/;

        /*- set id = composition.connections.index(me.parent) -*/

        /*- set frame_caps_symbol = c_symbol('frame_caps') -*/

        /*# Allocate frame objects to back the hardware dataport #*/
        static const seL4_CPtr /*? frame_caps_symbol ?*/[] = {
            /*- for cap in frame_caps -*/
                /*? cap ?*/,
            /*- endfor -*/
        };

        /*- for cap in frame_caps -*/
            __attribute__((used)) __attribute__((section("_dataport_frames")))
            dataport_frame_t /*? reg_interface_name ?*/_/*? loop.index0 ?*/ = {
                .paddr = /*? paddr + loop.index0 * page_size ?*/,
                .cap = /*? cap ?*/,
                .size = /*? page_size ?*/,
                .vaddr = &/*? dataport_symbol_name ?*/.content + /*? loop.index0 * page_size ?*/,
            };
        /*- endfor -*/

        /*# We only pull frame_caps from the stash. This is because only one caller of register_shared_variable
            should pass a frames parameter. By not stashing the frame_objs we ensure that only the original
            creator passed the frames, and everyone else will still have a None here #*/

        /*- if options.architecture in ('aarch32', 'arm_hyp', 'aarch64') -*/
        static int sel4_cache_op(seL4_CPtr frame_cap, seL4_Word start, seL4_Word end, dma_cache_op_t cache_op) {
            switch (cache_op) {
            case DMA_CACHE_OP_CLEAN:
                return seL4_ARM_Page_Clean_Data(frame_cap, start, end);
            case DMA_CACHE_OP_INVALIDATE:
                return seL4_ARM_Page_Invalidate_Data(frame_cap, start, end);
            case DMA_CACHE_OP_CLEAN_INVALIDATE:
                return seL4_ARM_Page_CleanInvalidate_Data(frame_cap, start, end);
            default:
                ZF_LOGF("Invalid cache_op %d", cache_op);
                return -1;
            }
        }
        /*- endif -*/

        /* Flush data corresponding to the dataport-relative address range from the CPU cache */
        int /*? reg_interface_name ?*/_flush_cache(size_t start_offset UNUSED, size_t size UNUSED, dma_cache_op_t cache_op UNUSED) {
        /*- if options.architecture in ('aarch32', 'arm_hyp', 'aarch64') -*/

            if (start_offset >= /*? size ?*/ || size > /*? size ?*/ || /*? size ?*/ - size < start_offset) {
                ZF_LOGE("Specified range is outside the bounds of the dataport");
                return -1;
            }

            size_t current_offset = start_offset;
            size_t end_offset = start_offset + size;

            while (current_offset < end_offset) {
                size_t frame_top = MIN(ROUND_UP(current_offset + 1, /*? macros.PAGE_SIZE ?*/), end_offset);
                seL4_CPtr frame_cap = /*? frame_caps_symbol ?*/[current_offset / /*? macros.PAGE_SIZE ?*/];
                size_t frame_start_offset = current_offset % /*? macros.PAGE_SIZE ?*/;
                size_t frame_end_offset = ((frame_top - 1) % /*? macros.PAGE_SIZE ?*/) + 1;
                int error = sel4_cache_op(frame_cap, frame_start_offset,  frame_end_offset, cache_op);
                if (error) {
                    ZF_LOGE("Cache flush syscall returned with error: %d", error);
                    return error;
                }
                current_offset = frame_top;
            }

        /*- endif -*/
            return 0;
        }

    /*- endfor -*/

/*- endif -*/

/*# ================== #*/
/*# Interrupts section #*/
/*# ================== #*/

/*# This section assumes that the `interrupts` binding's format follow those of the #*/
/*# ARM GIC (not v3), i.e. cell 1 = SPI, cell 2 = interrupt number and cell 3 the flag. #*/

/*- if interrupts is not none -*/
    /*- if is_extended_interrupts -*/
        /*- set num_interrupts = len(interrupts) // 4 -*/
    /*- else -*/
        /*- set num_interrupts = len(interrupts) // 3 -*/
    /*- endif -*/
    /*- if num_interrupts > 28 -*/
        /*# CAmkES has a maximum limit of 28 bits for badges, #*/
        /*# highly unlikely a device has greater than 28 #*/
        /*? raise(TemplateError('Device %s has more than 28 interrupts, this is more than we can support.') % (me.interface.name)) ?*/
    /*- endif -*/
    /*- set ntfn_obj = alloc_obj('%s_ntfn' % me.interface.name, seL4_NotificationObject) -*/
    /*- set root_ntfn = alloc_cap('%s_root_ntfn' % me.interface.name, ntfn_obj, read=True, write=True) -*/

    int /*? me.interface.name ?*/__run(void) {
        while (true) {
            seL4_Word badge = 0;
            seL4_Wait(/*? root_ntfn ?*/, &badge);

            /*# Generate the calls to the IRQ handling functions #*/
            /*- for i in range(0, num_interrupts) -*/
                /*- set bit = pow(2, i) -*/
                if (badge & /*? bit ?*/) {
                    /*? '%s_%d' % (me.interface.name, i) ?*/_handle();
                }
            /*- endfor -*/
        }

        UNREACHABLE();
    }

    /*- set irq_ntfn_pairs = [] -*/

    /*- for i in range(0, num_interrupts) -*/

        /*- set interrupt_ntfn = alloc_cap('%s_ntfn_%d' % (me.interface.name, i), ntfn_obj, read=True, write=True, badge=pow(2, i)) -*/

        /*- if is_extended_interrupts -*/
            /*- set _irq = interrupts[i * 3 + 2] -*/
            /*- set _irq_spi = interrupts[i * 3 + 1] -*/
        /*- else -*/
            /*- set _irq = interrupts[i * 3 + 1] -*/
            /*- set _irq_spi = interrupts[i * 3 + 0] -*/
        /*- endif -*/
        /*- if (isinstance(_irq_spi, numbers.Integral)) and (_irq_spi == 0) -*/
            /*- set _irq = _irq + 32 -*/
        /*- endif -*/
        /*- set irq = alloc('%s_irq_%d' % (me.interface.name, i), seL4_IRQHandler, number=_irq) -*/

        /*# Add the interrupt notification and IRQ handler to the list for later #*/
        /*- do irq_ntfn_pairs.append((interrupt_ntfn, irq)) -*/

        /*- set interrupt_interface_name = '%s_%d' % (me.interface.name, i) -*/

        int /*? interrupt_interface_name ?*/_acknowledge(void) {
            return seL4_IRQHandler_Ack(/*? irq ?*/);
        }

    /*- endfor -*/

    /*# Pair the IRQ handlers with their notification, this resolves the capdl loader issue #*/
    /*# where the notifications are badged after being paired with their respective handlers #*/
    void /*? me.interface.name ?*/__init(void) {
        int error = 0;
        /*- for (notification, handler) in irq_ntfn_pairs -*/
            error = seL4_IRQHandler_SetNotification(/*? handler ?*/, /*? notification ?*/);
            if (error) {
                assert(!"Failed to pair IRQ handler with notification");
            }
        /*- endfor -*/
    }

/*- endif -*/
