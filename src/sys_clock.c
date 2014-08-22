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
#include <time.h>

#define NS_IN_SEC 1000000000UL  //How many nanoseconds in one second.

int clk_get_time(void) __attribute__((weak));
long sys_clock_gettime(va_list ap)
{
	clockid_t clk = va_arg(ap, clockid_t);
	struct timespec *ts = va_arg(ap, struct timespec*);
	uint64_t curtime;

	if (clk_get_time && (clk == CLOCK_REALTIME) && ts) {
		curtime = clk_get_time();
		ts->tv_sec = curtime / NS_IN_SEC;
		ts->tv_nsec = curtime % NS_IN_SEC;
	} else {
		assert(!"sys_clock_gettime not implemented");
	}
	
	return 0;
}
