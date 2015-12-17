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
#include <stdio.h>
#include <stdint.h>

long sys_sigaction(va_list ap)
{
	printf("Warning: %s ignored.\n", __func__);
	return 0;
}

long sys_rt_sigaction(va_list ap)
{
	printf("Warning: %s ignored.\n", __func__);
	return 0;
}
