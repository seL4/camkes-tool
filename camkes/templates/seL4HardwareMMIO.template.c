/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <camkes/dataport.h>
#include <stddef.h>
#include <stdint.h>
#include <sel4/sel4.h>
/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set p = Perspective(dataport=me.from_interface.name) -*/
#define MMIO_ALIGN (1 << 12)
struct {
    char content[ROUND_UP_UNSAFE(sizeof(/*? show(me.from_interface.type) ?*/),
        PAGE_SIZE_4K)];
} /*? p['dataport_symbol'] ?*/
        __attribute__((aligned(MMIO_ALIGN)))
        __attribute__((section("ignore_/*? me.from_interface.name ?*/")))
        __attribute__((externally_visible));

volatile /*? show(me.from_interface.type) ?*/ * /*? me.from_interface.name ?*/ =
    (volatile /*? show(me.from_interface.type) ?*/ *) & /*? p['dataport_symbol'] ?*/;

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

int /*? me.from_interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    /*- set offset = c_symbol('offset') -*/
    off_t /*? offset ?*/ = (off_t)((uintptr_t)ptr - (uintptr_t)/*? me.from_interface.name ?*/);
    if (/*? offset ?*/ < sizeof(/*? show(me.from_interface.type) ?*/)) {
        p->id = /*? id ?*/;
        p->offset = /*? offset ?*/;
        return 0;
    } else {
        return -1;
    }
}

void * /*? me.from_interface.name ?*/_unwrap_ptr(dataport_ptr_t *p) {
    if (p->id == /*? id ?*/) {
        return (void*)((uintptr_t)/*? me.from_interface.name ?*/ + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}

/*- set p = Perspective(to_interface=me.to_interface.name) -*/
/*#Check if we have preserved enough virtual memory for the MMIO. #*/
/*- set attr = configuration[me.to_instance.name].get(p['hardware_attribute']) -*/
/*- if attr is not none -*/
    /*- set paddr, size = attr.strip('"').split(':') -*/
    _Static_assert(sizeof(/*? show(me.from_interface.type) ?*/) == /*? size ?*/, "Data type mismatch!");

    /*- set cached = configuration[me.to_instance.name].get(p['hardware_cached']) -*/
    /*- if cached is none -*/
        /*- set cached = False -*/
    /*- elif cached.lower() == 'true' -*/
        /*- set cached = True -*/
    /*- elif cached.lower() == 'false' -*/
        /*- set cached = False -*/
    /*- else -*/
        /*? raise(Exception("Value of %s.%s_cached must be either 'true' or 'false'. Got '%s'." %
                    (me.to_instance.name, me.to_interface.name, cached))) ?*/
    /*- endif -*/

    void * /*? me.from_interface.name ?*/_translate_paddr(
            uintptr_t paddr, size_t size) {
        if (paddr >= /*? paddr ?*/ && paddr + size <= /*? paddr ?*/ + /*? size ?*/) {
            return (void*)((uintptr_t)/*? me.from_interface.name ?*/ + (paddr - /*? paddr ?*/));
        }
        return NULL;
    }

    /*# Types and sizes of frames is hardware-specific #*/
    /*- if arch == 'arm' -*/
        /*- set large_frame_size = 1024 * 1024 -*/
        /*- set large_frame_type = seL4_ARM_SectionObject -*/
    /*- else -*/
        /*- set large_frame_size = 4 * 1024 * 1024 -*/
        /*- set large_frame_type = seL4_IA32_4M -*/
    /*- endif -*/

    /*# Convert from string to int #*/
    /*- if re.match('((0x[\da-fA-F]+)|([1-9]\d*))$', paddr) is none -*/
        /*? raise(Exception("Invalid physical address specified for %s.%s: %s\n" %
                    (me.to_instance.name, me.to_interface.name, paddr))) ?*/
    /*- endif -*/
    /*- if re.match('((0x[\da-fA-F]+)|([1-9]\d*))$', size) is none -*/
        /*? raise(Exception("Invalid size specified for %s.%s: %s\n" %
                    (me.to_instance.name, me.to_interface.name, size))) ?*/
    /*- endif -*/

    /*- set paddr = int(paddr, 0) -*/
    /*- set size = int(size, 0) -*/

    static const seL4_CPtr /*? me.from_interface.name ?*/_frame_caps[] = {
    /*# Allocate frame objects to back the hardware dataport #*/
    /*- if paddr % large_frame_size == 0 and size % large_frame_size == 0 -*/
        /*- set frame_size = large_frame_size -*/
        /*- set n_frames = size // large_frame_size -*/
        /*- for i in range(n_frames) -*/
            /*- set name = "large_frame_%s_%d (%s.%s)" % (me.from_instance.name, i, me.to_instance.name, me.to_interface.name) -*/
            /*- set offset = large_frame_size * i -*/
            /*- set frame_obj = alloc_obj(name, large_frame_type, paddr=(paddr + offset)) -*/
            /*- set frame_cap = alloc_cap(name, frame_obj) -*/
            /*? frame_cap ?*/,
        /*- endfor -*/
    /*- else -*/
        /*- set frame_size = PAGE_SIZE -*/
        /*- set n_frames = (size + PAGE_SIZE - 1) // PAGE_SIZE -*/
        /*- for i in range(n_frames) -*/
            /*- set name = "frame_%s_%d (%s.%s)" % (me.from_instance.name, i, me.to_instance.name, me.to_interface.name) -*/
            /*- set offset = PAGE_SIZE * i -*/
            /*- set frame_obj = alloc_obj(name, seL4_FrameObject, paddr=(paddr + offset)) -*/
            /*- set frame_cap = alloc_cap(name, frame_obj) -*/
            /*? frame_cap ?*/,
        /*- endfor -*/
    /*- endif -*/
    };

/*- endif -*/
