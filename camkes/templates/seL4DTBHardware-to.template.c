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
#include <camkes/irq.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <platsupport/io.h>
#include <platsupport/irq.h>
#include <utils/util.h>
#include <sel4/sel4.h>

/*- import 'dtb-query-common.template.c' as dtb_macros with context -*/

/*# Grab the DTB object made from the previous stages of the parsing #*/
/*- set configuration_name = '%s.%s' % (me.instance.name, me.interface.name) -*/
/*- set dtb_config = configuration[configuration_name].get('dtb') -*/
/*- if dtb_config is none -*/
    /*# DTB query hasn't been made, raise a fault #*/
    /*? raise(TemplateError('Missing DTB attribute, create a DTB query to attribute %s.dtb.' % (me.interface.name))) ?*/
/*- endif -*/
/*- set dtb_query = dtb_config.get('query')  -*/
/*- if dtb_query is none -*/
    /*# DTB path hasn't been passed, raise a fault #*/
    /*? raise(TemplateError('Missing DTB query, assign a DTB path to attribute %s.dtb.' % (me.interface.name))) ?*/
/*- endif -*/
/*- if len(dtb_query) != 1 -*/
    /*? raise(TemplateError('Invalid number of DTB paths, assign a single DTB path to attribute %s.dtb.' % (me.interface.name))) ?*/
/*- endif -*/
/*- if dtb_query[0] is none -*/
    /*? raise(TemplateError('Missing DTB path, assign a single DTB path to attribute %s.dtb.' % (me.interface.name))) ?*/
/*- endif -*/
/*- set dtb = dtb_query[0]  -*/

/*# Check if we want interrupts #*/
/*- set generate_interrupts = configuration[configuration_name].get('generate_interrupts', none) -*/

/*# ================ #*/
/*# Register section #*/
/*# ================ #*/

/*? dtb_macros.parse_dtb_node_reg(dtb) ?*/
/*- set reg_set = pop('reg_set') -*/
/*- set cached = configuration[configuration_name].get('hardware_cached', False) -*/

/*- for (paddr, size) in reg_set -*/

        /*# Get the next multiple of 4K that can fit the register #*/
        /*- set size = macros.next_page_multiple(size, options.architecture) -*/
        /*- set page_size = macros.get_page_size(size, options.architecture) -*/
        /*- set page_size_bits = int(math.log(page_size, 2)) -*/

        /*- set dataport_symbol_name = "from_%d_%s_data" % (loop.index0, me.interface.name) -*/
        struct {
            char content[ROUND_UP_UNSAFE(/*? size ?*/,
                SIZE_BITS_TO_BYTES(/*? page_size_bits ?*/))];
        } /*? dataport_symbol_name ?*/
                ALIGN(/*? page_size ?*/)
                SECTION("align_/*? page_size_bits ?*/bit")
                VISIBLE
                USED;

        /*- set reg_interface_name = '%s_%d' % (me.interface.name, loop.index0) -*/

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
                .vaddr = &(/*? dataport_symbol_name ?*/.content[/*? loop.index0 * page_size ?*/]),
            };
        /*- endfor -*/

        /*# We only pull frame_caps from the stash. This is because only one caller of register_shared_variable
            should pass a frames parameter. By not stashing the frame_objs we ensure that only the original
            creator passed the frames, and everyone else will still have a None here #*/


        /* Flush data corresponding to the dataport-relative address range from the CPU cache */
        int /*? reg_interface_name ?*/_flush_cache(size_t start_offset UNUSED, size_t size UNUSED, dma_cache_op_t cache_op UNUSED) {
            return camkes_dataport_flush_cache(start_offset, size, 
                                               (uintptr_t) &/*? dataport_symbol_name ?*/.content,
                                               /*? size ?*/, cache_op);
        }

/*- endfor -*/

/*# ================== #*/
/*# Interrupts section #*/
/*# ================== #*/

/*- if generate_interrupts -*/

    /*- set ntfn_obj = alloc_obj('%s_ntfn' % me.interface.name, seL4_NotificationObject) -*/
    /*- set root_ntfn = alloc_cap('%s_root_ntfn' % me.interface.name, ntfn_obj, read=True, write=True) -*/

    /*- set irq_ntfn_pairs = [] -*/

    /*- set irq_handler_pairs = [] -*/

    /*- set interrupt_struct_prefix = '%s_irq' % (me.interface.name) -*/

    /*# CAmkES has a maximum limit of 28 bits for badges, #*/
    /*# highly unlikely a device has greater than 28 #*/
    /*? dtb_macros.parse_dtb_node_interrupts(dtb, 28) ?*/
    /*- set irq_set = pop('irq_set') -*/

    /*- for (_irq, i) in zip(irq_set, range(0, len(irq_set)))  -*/

        /*- set interrupt_ntfn = alloc_cap('%s_ntfn_%d' % (me.interface.name, i), ntfn_obj, read=True, write=True, badge=pow(2, i)) -*/

        /*- set irq = alloc('%s_irq_%d' % (me.interface.name, i), seL4_IRQHandler, number=_irq) -*/

        /*# Add the interrupt number to the IRQ num list for later #*/
        /*- do irq_handler_pairs.append((_irq, irq)) -*/

        /*# Add the interrupt notification and IRQ handler to the list for later #*/
        /*- do irq_ntfn_pairs.append((interrupt_ntfn, irq)) -*/

        /*- set interrupt_interface_name = '%s_%d' % (me.interface.name, i) -*/

        /*# Add an entry to the allocated_irqs ELF section #*/
        static allocated_irq_t /*? interrupt_struct_prefix ?*/_/*? i ?*/ = {
            .irq_handler = /*? irq ?*/,
            .irq = { .type = PS_INTERRUPT, .irq = { .number = /*? _irq ?*/ }},
            .is_allocated = false,
            .callback_fn = NULL,
            .callback_data = NULL
        };
        USED SECTION("_allocated_irqs")
        allocated_irq_t * /*? interrupt_struct_prefix ?*/_/*? i ?*/_ptr = &/*? interrupt_struct_prefix ?*/_/*? i ?*/;

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

    /*# Generate IRQ acknowledgement code #*/
    int /*? me.interface.name ?*/_irq_acknowledge(ps_irq_t *irq) {
        /* Sanity checking */
        if (!irq) {
            return -1;
        }
        assert(irq->type == PS_INTERRUPT);
        switch (irq->irq.number) {
        /*- for (irq_num, handler) in irq_handler_pairs -*/
            case /*? irq_num ?*/:
                return seL4_IRQHandler_Ack(/*? handler ?*/);
        /*- endfor -*/
            default:
                /* Passed in an invalid IRQ number */
                return -1;
        }
    }

    static int /*? me.interface.name ?*/_irq_acknowledge_wrapper(void *ack_data) {
        ps_irq_t *irq = (ps_irq_t *) ack_data;
        return /*? me.interface.name ?*/_irq_acknowledge(irq);
    }

    int /*? me.interface.name ?*/__run(void) {
        while (true) {
            seL4_Word badge = 0;
            seL4_Wait(/*? root_ntfn ?*/, &badge);

            /*# Generate the calls to the IRQ handling functions #*/
            /*- for i in range(0, len(irq_set)) -*/
                /*- set bit = pow(2, i) -*/
                if (badge & /*? bit ?*/) {
                    void /*? me.interface.name ?*/_irq_handle(ps_irq_t *irq) WEAK;
                    ps_irq_t irq = { .type = PS_INTERRUPT, .irq = { .number = /*? irq_handler_pairs[i][0] ?*/}};
                    if (/*? me.interface.name ?*/_irq_handle && /*? interrupt_struct_prefix ?*/_/*? i ?*/.is_allocated) {
                        ZF_LOGF("Both IRQ interface and 'handle' function is in use for interrupt /*? i ?*/! "
                                "These are mutually exclusive, use one or the other.");
                    } else if (/*? me.interface.name ?*/_irq_handle) {
                        /*? me.interface.name ?*/_irq_handle(&irq);
                    } else if (/*? interrupt_struct_prefix ?*/_/*? i ?*/.is_allocated) {
                        /*? interrupt_struct_prefix ?*/_/*? i ?*/.callback_fn(/*? interrupt_struct_prefix ?*/_/*? i ?*/.callback_data, 

                                                                              /*? me.interface.name ?*/_irq_acknowledge_wrapper,

                                                                              &irq);
                    } else {
                        ZF_LOGE("No mechanism exists to handle this interrupt, this interrupt will be ignored");
                    }
                }
            /*- endfor -*/
        }

        UNREACHABLE();
    }

/*- endif -*/
