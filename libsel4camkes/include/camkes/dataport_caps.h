/*
 * Copyright 2019, Data61
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

#include <stdlib.h>
#include <sel4/sel4.h>

/* An interface for accessing caps of a dataport on the "to" side
 * of a seL4SharedDataWithCaps connection.
 */

typedef seL4_CPtr(*dataport_get_nth_frame_cap_fn)(unsigned int n);
typedef unsigned int (*dataport_get_id_fn)(void);
typedef unsigned int (*dataport_get_num_frame_caps_fn)(void);
typedef seL4_CPtr *(*dataport_get_frame_caps_fn)(void);
typedef void (*dataport_free_frame_caps_fn)(seL4_CPtr *);
typedef size_t (*dataport_get_size_fn)(void);
typedef seL4_CapRights_t (*dataport_get_rights_fn)(void);

typedef struct {
    dataport_get_nth_frame_cap_fn get_nth_frame_cap;
    dataport_get_id_fn get_id;
    dataport_get_num_frame_caps_fn get_num_frame_caps;
    dataport_get_frame_caps_fn get_frame_caps;
    dataport_free_frame_caps_fn free_frame_caps;
    dataport_get_size_fn get_size;
    dataport_get_rights_fn get_rights;
} dataport_caps_handle_t;

static inline seL4_CPtr dataport_get_nth_frame_cap(dataport_caps_handle_t *d, unsigned int n)
{
    return d->get_nth_frame_cap(n);
}

static inline unsigned int dataport_get_id(dataport_caps_handle_t *d)
{
    return d->get_id();
}

static inline unsigned int dataport_get_num_frame_caps(dataport_caps_handle_t *d)
{
    return d->get_num_frame_caps();
}

static inline seL4_CPtr *dataport_get_frame_caps(dataport_caps_handle_t *d)
{
    return d->get_frame_caps();
}

static inline void dataport_free_frame_caps(dataport_caps_handle_t *d, seL4_CPtr *frame_caps)
{
    return d->free_frame_caps(frame_caps);
}

static inline size_t dataport_get_size(dataport_caps_handle_t *d)
{
    return d->get_size();
}

static inline seL4_CapRights_t dataport_get_rights(dataport_caps_handle_t *d)
{
    return d->get_rights();
}
