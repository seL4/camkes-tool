/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef __LIBSEL4MUSLCCAMKES_H__
#define __LIBSEL4MUSLCCAMKES_H__

#include <utils/page.h>
#include <camkes/dataport.h>

#define FILE_TYPE_SOCKET  1

/* CAmkES dataport for socket interface. */
extern Buf* sock_data __attribute__((weak));

#endif
