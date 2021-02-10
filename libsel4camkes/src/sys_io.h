/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <utils/page.h>
#include <camkes/dataport.h>

#define FILE_TYPE_SOCKET  1

/* CAmkES dataport for socket interface. */
extern Buf *sock_data __attribute__((weak));
