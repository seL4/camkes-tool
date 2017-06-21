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

#pragma once

#include <utils/util.h>

#define /*? me.interface.name ?*/_release() COMPILER_MEMORY_RELEASE()
#define /*? me.interface.name ?*/_acquire() COMPILER_MEMORY_ACQUIRE()
