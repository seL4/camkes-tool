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

#ifndef __LIBSEL4MUSLCCAMKES_H__
#define __LIBSEL4MUSLCCAMKES_H__

#include <utils/page.h>
#include <camkes/dataport.h>

#define FILE_TYPE_SOCKET  1

/* CAmkES dataport for socket interface. */
extern Buf* sock_data __attribute__((weak));

#endif
