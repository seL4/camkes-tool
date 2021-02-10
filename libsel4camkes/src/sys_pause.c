/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdarg.h>
#include <assert.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <utils/util.h>

long camkes_sys_pause(va_list ap UNUSED)
{

    /* Suspend ourselves. This will cap fault if a setup routine has not saved
     * our TCB cap in the TLS region.
     */
    seL4_TCB_Suspend(camkes_get_tls()->tcb_cap);

    /* We expect to never be woken up. */
    UNREACHABLE();
    return 0;
}
