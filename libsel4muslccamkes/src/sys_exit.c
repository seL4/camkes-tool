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
#include <sel4/sel4.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <camkes/tls.h>
#include <utils/util.h>

static void
sel4_abort(void)
{
    /* Suspend ourselves. This will cap fault if a setup routine has not saved
     * our TCB cap in the TLS region.
     */
    seL4_TCB_Suspend(camkes_get_tls()->tcb_cap);

    /* We expect to never be woken up. */
    while (1); /* Shut the compiler up about noreturn. */
}

long
sys_exit(va_list ap UNUSED)
{
    abort();
    return 0;
}

long
sys_rt_sigprocmask(va_list ap UNUSED)
{
    return 0;
}

long
sys_gettid(va_list ap UNUSED)
{
    return 0;
}

long
sys_getpid(va_list ap UNUSED)
{
    return 1234;
}

long
sys_tgkill(va_list ap UNUSED)
{
    sel4_abort();
    return 0;
}

long
sys_tkill(va_list ap UNUSED)
{
    sel4_abort();
    return 0;
}

long
sys_exit_group(va_list ap UNUSED)
{
    return 0;
}
