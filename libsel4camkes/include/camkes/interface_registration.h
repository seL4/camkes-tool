/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <platsupport/io.h>
#include <platsupport/interface_registration.h>

int camkes_interface_registration_ops(ps_interface_registration_ops_t *interface_ops, ps_malloc_ops_t *malloc_ops);
