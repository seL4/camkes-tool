/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <assert.h>
#include <stdarg.h>
#include <assert.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <utils/util.h>

long sys_pause(va_list ap UNUSED) {

    /* Suspend ourselves. This will cap fault if a setup routine has not saved
     * our TCB cap in the TLS region.
     */
    seL4_TCB_Suspend(camkes_get_tls()->tcb_cap);

    /* We expect to never be woken up. */
    UNREACHABLE();
    return 0;
}
