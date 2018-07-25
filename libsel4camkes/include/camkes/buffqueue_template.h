/*
 * Copyright 2018, Data61
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

#include <buffqueue.h>
#include <camkes/buffqueue.h>

int camkes_register_buffqueue_channel(int buffqueue_id, size_t size, volatile void *buf, notify_fn_t notify, buffqueue_role_t role);
