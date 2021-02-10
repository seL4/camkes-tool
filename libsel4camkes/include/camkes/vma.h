/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>

struct camkes_vma {

    /* Dimensions of the region. It would seem to make more sense to give a size than an end
     * pointer, however it is then not possible to construct the `camkes_vmas` array at
     * compile-time.
     */
    void *start;
    void *end;

    /* Permissions. Note that these are the *logical* permissions the region has. It is possible
     * that two regions overlap a single page, and thus the permissions of this page are the union
     * of their permissions. Essentially the permissions of a VMA are the minimum permissions you
     * can expect the memory in that region to have. 0 for all these fields means the region is
     * deliberately unmapped memory.
     */
    bool read;
    bool write;
    bool execute;

    /* Extended attributes. */
    bool cached;

    /* Friendly name of the region. This is only for debugging purposes and you should not rely on
     * this field containing a string formatted in any particular way.
     */
    const char *name;

};

/* Address space information about the current component. Note that this is defined in generated
 * code. Users should not assume regions will appear in any particular order.
 */
extern const struct camkes_vma camkes_vmas[];

/* Number of members in the above array. */
extern const size_t camkes_vmas_size;
