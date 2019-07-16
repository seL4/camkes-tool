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

#pragma once

#include <platsupport/irq.h>
#include <platsupport/io.h>
#include <stdint.h>
#include <stdbool.h>
#include <sel4/sel4.h>
#include <utils/attribute.h>

/*
 * This struct describes the interrupts that were allocated by CAmkES.
 *
 * Pointers to instances of this struct is intended to be located inside an ELF
 * section.
 */
struct allocated_irq {
    seL4_CPtr irq_handler;
    ps_irq_t irq;
    bool is_allocated;
    irq_callback_fn_t callback_fn;
    void *callback_data;
};
typedef struct allocated_irq allocated_irq_t;

/*
 * NOTE: This implementation of the platsuport IRQ interface is not thread-safe.
 */

/*
 * Initialises the IRQ interface. The number of interrupts that can be
 * registered is the number of interrupts allocated by CAmkES.
 *
 * @param irq_ops Interface to fill in
 * @param malloc_ops Malloc interface that is used to allocate memory for the IRQ interface
 * @param max_ntfn_ids Maximum number of notifications that can be provided
 *
 * @return 0 on success, otherwise an error code
 */
int camkes_irq_ops(ps_irq_ops_t *irq_ops);
