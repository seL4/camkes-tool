/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <autoconf.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <bits/errno.h>
#include <camkes/tls.h>
#include <sel4utils/arch/util.h>
#include <utils/util.h>

long camkes_sys_set_tid_address(va_list ap UNUSED) {
    /* We ignore the input argument (an address to replace the current value of `clear_child_tid`,
     * but `set_tid_address` is documented as always succeeding, so we pretend we saved it.
     */
    return (long)camkes_get_tls()->thread_index;
}
