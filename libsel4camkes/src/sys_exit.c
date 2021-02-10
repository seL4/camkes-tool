/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <sel4/sel4.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <camkes/pid.h>
#include <camkes/tls.h>
#include <utils/util.h>

static void sel4_abort(void)
{
    /* Suspend ourselves. This will cap fault if a setup routine has not saved
     * our TCB cap in the TLS region.
     */
    seL4_TCB_Suspend(camkes_get_tls()->tcb_cap);

    /* We expect to never be woken up. */
    while (1); /* Shut the compiler up about noreturn. */
}

long camkes_sys_exit(va_list ap UNUSED)
{
    abort();
    return 0;
}

long camkes_sys_gettid(va_list ap UNUSED)
{
    return (long)camkes_get_tls()->thread_index;
}

long camkes_sys_getpid(va_list ap UNUSED)
{
    return (long)camkes_pid;
}

long camkes_sys_getppid(va_list ap UNUSED)
{
    /* We consider the CapDL initialiser to have PID 1 and to be the parent of all component
     * instances.
     */
    return 1L;
}

long camkes_sys_tgkill(va_list ap UNUSED)
{
    sel4_abort();
    return 0;
}

long camkes_sys_tkill(va_list ap UNUSED)
{
    sel4_abort();
    return 0;
}
