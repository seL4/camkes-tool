/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <utils/util.h>

long camkes_sys_sigaction(va_list ap UNUSED)
{
    LOG_INFO("Warning: %s ignored.\n", __func__);
    return 0;
}

long camkes_sys_rt_sigaction(va_list ap UNUSED)
{
    LOG_INFO("Warning: %s ignored.\n", __func__);
    return 0;
}
