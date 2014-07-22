/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*- import 'macros.jinja' as macros -*/

#include <camkes/dataport.h>
/*? macros.show_includes(me.from_instance.type.includes) ?*/

/*- set p = Perspective(to_interface=me.to_interface.name) -*/
/*#Check if we have preserved enough virtual memory for the MMIO. #*/
/*- for s in configuration.settings -*/
    /*- if s.instance == me.to_instance.name -*/
        /*- if s.attribute == p['hardware_attribute'] -*/
            /*- set paddr, size = s.value.strip('"').split(':') -*/
            _Static_assert(sizeof(/*? show(me.from_interface.type) ?*/) == /*? size ?*/, "Data type mismatch!");
        /*- endif -*/
    /*- endif -*/
/*- endfor -*/

/* Actual dataport is emitted in the per-component template. */
/*- set p = Perspective(dataport=me.from_interface.name) -*/
extern char /*? p['dataport_symbol'] ?*/[];
extern volatile /*? show(me.from_interface.type) ?*/ * /*? me.from_interface.name ?*/;

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

int /*? me.from_interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    /*- set offset = c_symbol('offset') -*/
    off_t /*? offset ?*/ = (off_t)((uintptr_t)ptr - (uintptr_t)/*? p['dataport_symbol'] ?*/);
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
        return (void*)((uintptr_t)/*? p['dataport_symbol'] ?*/ + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}
