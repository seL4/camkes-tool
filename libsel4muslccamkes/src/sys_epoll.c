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
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <utils/util.h>

long sys_epoll_create(va_list ap)
{
	assert(!"sys_epoll_create not implemented");
	return -ENOSYS;
}

long sys_epoll_ctl(va_list ap)
{
	assert(!"sys_epoll_ctl not implemented");
	return -ENOSYS;
}

long sys_epoll_wait(va_list ap)
{
	assert(!"sys_epoll_wait not implemented");
	return -ENOSYS;
}

