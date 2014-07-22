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
#include <stdlib.h>

/*? macros.show_includes(me.from_instance.type.includes) ?*/

/* Actual dataport is emitted in the per-component template. */
/*- set p = Perspective(dataport=me.from_interface.name) -*/
extern char /*? p['dataport_symbol'] ?*/[ROUND_UP_UNSAFE(sizeof(/*? show(me.from_interface.type) ?*/), PAGE_SIZE_4K)];
extern volatile /*? show(me.from_interface.type) ?*/ * /*? me.from_interface.name ?*/;

int /*? me.from_interface.name ?*/__run(void) {
    /* Nothing required. */
    return 0;
}

int /*? me.from_interface.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr) {
    if ((uintptr_t)ptr < (uintptr_t)/*? p['dataport_symbol'] ?*/ ||
            (uintptr_t)ptr >= (uintptr_t)/*? p['dataport_symbol'] ?*/ + sizeof(/*? show(me.from_interface.type) ?*/)) {
        return -1;
    }
    p->id = /*? id ?*/;
    p->offset = (off_t)((uintptr_t)ptr - (uintptr_t)/*? p['dataport_symbol'] ?*/);
    return 0;
}

void * /*? me.from_interface.name ?*/_unwrap_ptr(dataport_ptr_t *p) {
    if (p->id == /*? id ?*/) {
        return (void*)((uintptr_t)/*? p['dataport_symbol'] ?*/ + (uintptr_t)p->offset);
    } else {
        return NULL;
    }
}
