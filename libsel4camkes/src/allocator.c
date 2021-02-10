/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <camkes/allocator.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <stdlib.h>

/* Super dumb (and simple) bookkeeping where we keep everything in a single
 * linked-list and search this every time we need to alloc/free.
 */
typedef struct _node {
    seL4_ObjectType type;
    size_t size;
    seL4_CPtr ptr;
    bool used;
    unsigned attributes;

    struct _node *next;
} node_t;
static node_t *resources;

int camkes_provide(seL4_ObjectType type, seL4_CPtr ptr, size_t size,
                   unsigned attributes)
{
    node_t *n = calloc(1, sizeof(*n));
    if (n == NULL) {
        return -1;
    }

    n->type = type;
    n->size = size;
    n->ptr = ptr;
    n->attributes = attributes;
    n->next = resources;
    resources = n;
    return 0;
}

seL4_CPtr camkes_alloc(seL4_ObjectType type, size_t size, unsigned flags)
{
    for (node_t *n = resources; n != NULL; n = n->next) {
        if (n->type == type && !n->used && (n->attributes & flags) == flags &&
            (size == 0 || size == n->size)) {
            n->used = true;
            return n->ptr;
        }
    }
    return seL4_CapNull;
}

void camkes_free(seL4_CPtr ptr)
{
    for (node_t *n = resources; n != NULL; n = n->next) {
        if (n->ptr == ptr) {
            assert(n->used && "double free of a cap pointer");
            n->used = false;
            return;
        }
    }
    assert(!"free of a cap pointer that was never allocated");
}
