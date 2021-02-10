/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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


struct global_notification_irq_handler {
    seL4_Word badge;
    ps_irq_acknowledge_fn_t ack_fun;
    allocated_irq_t *allocated_ref;
};
typedef struct global_notification_irq_handler global_notification_irq_handler_t;

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


/* Event handler function for processing notification received on global_endpoint connector
 * notification object.
 *
 * @param badge Badge received from reading notification object. Badge is bitwise compared
 *              against badge values registered by global_notification_irq_handler_t entry.
 *
 * @return 0 on success, otherwise an error code
 */
int camkes_handle_global_endpoint_irq(seL4_Word badge);
