/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <camkes.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils/util.h>
#include <platsupport/irq.h>
#include <camkes/irq.h>

/*? macros.show_includes(me.instance.type.includes) ?*/
/*- set ntfn_obj = alloc_obj('ntfn', seL4_NotificationObject) -*/
/*- set ntfn = alloc_cap('ntfn', ntfn_obj, read=True) -*/

/*- set type_attr = '%s_irq_type' % me.parent.from_interface.name -*/
/*- set type = configuration[me.parent.from_instance.name].get(type_attr, 'simple') -*/

/*- if type == 'simple' -*/
    /*- set attr = '%s_irq_number' % me.parent.from_interface.name -*/
    /*- set _irq = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if _irq is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(_irq, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set spi_attr = '%s_spi_number' % me.parent.from_interface.name -*/
    /*- set _irq_spi = configuration[me.parent.from_instance.name].get(spi_attr) -*/
    /*- if (isinstance(_irq_spi, numbers.Integral)) and (_irq_spi == 0) -*/
        /*- set _irq = _irq + 32 -*/
    /*- endif -*/
    /*- set irq = alloc('irq', seL4_IRQHandler, number=_irq, notification=my_cnode[ntfn]) -*/
/*- elif type in ['arm'] -*/
    /*- set attr = '%s_irq_trigger' % me.parent.from_interface.name -*/
    /*- set trigger = configuration[me.parent.from_instance.name].get(attr, "level") -*/
    /*- if trigger == "level" -*/
        /*- set trigger = seL4_ARM_IRQ_LEVEL -*/
        /*- set sel4_trigger_param = 0 -*/
    /*- elif trigger == "edge" -*/
        /*- set trigger = seL4_ARM_IRQ_EDGE -*/
        /*- set sel4_trigger_param = 1 -*/
    /*- else -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ trigger mode can only be "edge" or "level" but is set to: %s' % (me.parent.from_instance.name, attr, trigger))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_number' % me.parent.from_interface.name -*/
    /*- set _irq = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if _irq is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(_irq, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ number is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_target' % me.parent.from_interface.name -*/
    /*- set target = configuration[me.parent.from_instance.name].get(attr, 0) -*/
    /*- if not isinstance(target, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a target core is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set irq = alloc('irq', seL4_IRQHandler, number=_irq, trigger=trigger, target=target, notification=my_cnode[ntfn]) -*/
/*- elif type in ['ioapic','isa','pci'] -*/
    /*- if type == 'isa' -*/
        /*- set level = 0 -*/
        /*- set polarity = 0 -*/
    /*- elif type == 'pci' -*/
        /*- set level = 1 -*/
        /*- set polarity = 1 -*/
    /*- else -*/
        /*- set attr = '%s_irq_level' % me.parent.from_interface.name -*/
        /*- set level = configuration[me.parent.from_instance.name].get(attr) -*/
        /*- if level is none -*/
            /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC interrupt level is not defined' % (me.parent.from_instance.name, attr))) ?*/
        /*- endif -*/
        /*- if not isinstance(level, numbers.Integral) -*/
            /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC interrupt level is not an integer' % (me.parent.from_instance.name, attr))) ?*/
        /*- endif -*/
        /*- set attr = '%s_irq_polarity' % me.parent.from_interface.name -*/
        /*- set polarity = configuration[me.parent.from_instance.name].get(attr) -*/
        /*- if polarity is none -*/
            /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC interrupt polarity is not defined' % (me.parent.from_instance.name, attr))) ?*/
        /*- endif -*/
        /*- if not isinstance(polarity, numbers.Integral) -*/
            /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC interrupt polarity is not an integer' % (me.parent.from_instance.name, attr))) ?*/
        /*- endif -*/
    /*- endif -*/
    /*- set attr = '%s_irq_ioapic' % me.parent.from_interface.name -*/
    /*- set ioapic = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if ioapic is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC controller number is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(ioapic, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC controller number is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_ioapic_pin' % me.parent.from_interface.name -*/
    /*- set ioapic_pin = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if ioapic_pin is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC pin number is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(ioapic_pin, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IOAPIC pin number is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_vector' % me.parent.from_interface.name -*/
    /*- set vector = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if vector is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ vector is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(vector, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ vector is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set irq = alloc('irq', seL4_IRQHandler, vector=vector, ioapic=ioapic, ioapic_pin=ioapic_pin, level=level, polarity=polarity, notification=my_cnode[ntfn]) -*/
/*- elif type == 'msi' -*/
    /*- set attr = '%s_irq_handle' % me.parent.from_interface.name -*/
    /*- set handle = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if handle is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an MSI handle is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(handle, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an MSI handle is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_pci_bus' % me.parent.from_interface.name -*/
    /*- set pci_bus = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if pci_bus is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI bus is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(pci_bus, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI bus is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_pci_dev' % me.parent.from_interface.name -*/
    /*- set pci_dev = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if pci_dev is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI device is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(pci_dev, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI device is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_pci_fun' % me.parent.from_interface.name -*/
    /*- set pci_fun = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if pci_fun is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI function is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(pci_fun, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify a PCI function is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set attr = '%s_irq_vector' % me.parent.from_interface.name -*/
    /*- set vector = configuration[me.parent.from_instance.name].get(attr) -*/
    /*- if vector is none -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ vector is not defined' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- if not isinstance(vector, numbers.Integral) -*/
        /*? raise(TemplateError('Setting %s.%s that should specify an IRQ vector is not an integer' % (me.parent.from_instance.name, attr))) ?*/
    /*- endif -*/
    /*- set irq = alloc('irq', seL4_IRQHandler, vector=vector, handle=handle, pci_bus=pci_bus, pci_dev=pci_dev, pci_fun=pci_fun, notification=my_cnode[ntfn]) -*/
/*- else -*/
    /*? raise(TemplateError('Unknown irq type specified by %s.%s' % (me.parent.from_instance.name, type_attr))) ?*/
/*- endif -*/

/*# Add an entry to the allocated_irqs ELF section #*/
/*- set irq_struct_name = '%s_irq' % me.interface.name -*/
static allocated_irq_t /*? irq_struct_name ?*/ = {
    .irq_handler = /*? irq ?*/,
/*- if type == 'simple' -*/
    .irq = { .type = PS_INTERRUPT, .irq = { .number = /*? _irq ?*/ }},
/*- elif type in ['ioapic','isa','pci'] -*/
    .irq = { .type = PS_IOAPIC, .ioapic = { .ioapic = /*? ioapic ?*/, .pin = /*? ioapic_pin ?*/,
                                            .level = /*? level ?*/, .polarity = /*? polarity ?*/,
                                            .vector = /*? vector ?*/ }},
/*- elif type == 'msi' -*/
    .irq = { .type = PS_MSI, .msi = { .pci_bus = /*? pci_bus ?*/, .pci_dev = /*? pci_dev ?*/,
                                      .pci_func = /*? pci_fun ?*/, .handle = /*? handle ?*/,
                                      .vector = /*? vector ?*/ }},
/*- elif type == 'arm' -*/
    .irq = { .type = PS_TRIGGER, .cpu = { .trigger = /*? trigger.value ?*/, .cpu_idx= /*? target ?*/, .number = /*? _irq ?*/ }},
/*- endif -*/
    .is_allocated = false,
    .callback_fn = NULL,
    .callback_data = NULL
};
USED SECTION("_allocated_irqs")
allocated_irq_t * /*? irq_struct_name ?*/_ptr = &/*? irq_struct_name ?*/;

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

static int /*? me.interface.name ?*/_acknowledge_cb(UNUSED void* cookie) {
    return seL4_IRQHandler_Ack(/*? irq ?*/);
}

int /*? me.interface.name ?*/__run(void) {
    while (true) {
        seL4_Wait(/*? ntfn ?*/, NULL);
        if (/*? me.interface.name ?*/_handle && /*? irq_struct_name ?*/.is_allocated) {
            ZF_LOGF("Both IRQ interface and 'handle' function is in use! "
                    "These are mutually exclusive, use one or the other.");
        } else if (/*? me.interface.name ?*/_handle) {
            /*? me.interface.name ?*/_handle();
        } else if (/*? irq_struct_name ?*/.is_allocated) {
            /*? irq_struct_name ?*/.callback_fn(/*? irq_struct_name ?*/.callback_data, 
                                                /*? me.interface.name ?*/_acknowledge_cb,
                                                NULL);
        } else {
            ZF_LOGE("No mechanism exists to handle this interrupt, it will be ignored");
        }
    }

    UNREACHABLE();
}
