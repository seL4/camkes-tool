/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <assert.h>
#include <camkes.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils/util.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*- set attr = '%s_irq_number' % me.parent.from_interface.name -*/
/*- set aep_obj = alloc_obj('aep', seL4_AsyncEndpointObject) -*/
/*- set aep = alloc_cap('aep', aep_obj, read=True) -*/
/*- set _irq = configuration[me.parent.from_instance.name].get(attr) -*/
/*- if _irq is none -*/
  /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not defined' % (me.parent.from_instance.name, attr))) ?*/
/*- endif -*/
/*- if not isinstance(_irq, numbers.Integral) -*/
  /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not an integer' % (me.parent.from_instance.name, attr))) ?*/
/*- endif -*/
/*- set irq = alloc('irq', seL4_IRQControl, number=_irq, aep=my_cnode[aep]) -*/

int /*? me.interface.name ?*/__run(void) {
    while (true) {
        (void)seL4_Wait(/*? aep ?*/, NULL);
        /*? me.interface.name ?*/_handle();
    }

    UNREACHABLE();
}

int /*? me.interface.name ?*/_poll(void) {
    assert(!"not implemented for this connector");
    return 0;
}

void /*? me.interface.name ?*/_wait(void) {
    assert(!"not implemented for this connector");
    while (true);
}

int /*? me.interface.name ?*/_reg_callback(void (*callback)(void*) UNUSED,
        void *arg UNUSED) {
    assert(!"not implemented for this connector");
    return -1;
}

int /*? me.interface.name ?*/_acknowledge(void) {
    return seL4_IRQHandler_Ack(/*? irq ?*/);
}
