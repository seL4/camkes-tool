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

/* IO port/device functionality. This is meant for interaction with
 * libplatsupport infrastructure.
 */

#include <assert.h>
#include <camkes/dma.h>
#include <camkes/io.h>
#include <platsupport/io.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/* The following functions are generated in the component-wide template. */
extern void *camkes_io_map(void *cookie, uintptr_t paddr, size_t size,
    int cached, ps_mem_flags_t flags);
extern int camkes_io_port_in(void *cookie, uint32_t port, int io_size,
    uint32_t *result);
extern int camkes_io_port_out(void *cookie, uint32_t port, int io_size,
    uint32_t val);

/* Basic linked-list implementation. */
typedef struct ll_ {
    void *data;
    struct ll_ *next;
} ll_t;

static UNUSED int ll_prepend(ll_t **list, const void *data) {
    ll_t *node = malloc(sizeof *node);
    if (node == NULL) {
        return -1;
    }
    node->data = (void*)data;
    node->next = *list;
    *list = node;
    return 0;
}

static UNUSED int ll_remove(ll_t **list, const void *data) {
    for (ll_t **l = list; *l != NULL; l = &(*l)->next) {
        if ((*l)->data == data) {
            /* found it */
            ll_t *temp = *l;
            *l = (*l)->next;
            free(temp);
            return 0;
        }
    }
    return -1;
}

typedef struct {
    ps_io_map_fn_t map;
    ll_t *mapped;
} cookie_t;

/* Debug wrapper for IO map. This function calls the underlying map function
 * and tracks results for the purpose of catching illegal unmapping operations.
 * Note that this function is unused when NDEBUG is defined.
 */
static UNUSED void * io_map(void *cookie, uintptr_t paddr, size_t size,
        int cached, ps_mem_flags_t flags) {

    /* Call the real IO map function. */
    cookie_t *c = cookie;
    void *p = c->map(NULL, paddr, size, cached, flags);

    if (p != NULL) {
        /* The IO map function gave us a successful result; track this pointer
         * to lookup during unmapping.
         */
        if (ll_prepend(&c->mapped, p) != 0) {
            LOG_ERROR("failed to track mapped IO pointer %p\n", p);
        }
    }

    return p;
}

static int UNUSED pointer_compare(void *a, void *b) {
    uintptr_t p = (uintptr_t)a;
    uintptr_t q = (uintptr_t)b;
    if (p > q) {
        return 1;
    } else if (p < q) {
        return -1;
    } else {
        return 0;
    }
}

/* We never unmap anything. */
static void io_unmap(void *cookie UNUSED, void *vaddr UNUSED, size_t size UNUSED) {
#ifndef NDEBUG
    cookie_t *c = cookie;
    /* Make sure we previously mapped the pointer the caller gave us. */
    if (ll_remove(&c->mapped, vaddr) != 0) {
        LOG_ERROR("unmapping an IO pointer that was not previously mapped: %p\n",
            vaddr);
    }
#endif
}

int camkes_io_mapper(ps_io_mapper_t *mapper) {
    assert(mapper != NULL);
#ifdef NDEBUG
    mapper->cookie = NULL;
    mapper->io_map_fn = camkes_io_map;
#else
    cookie_t *c = malloc(sizeof(*c));
    if (c == NULL) {
        return -1;
    }
    c->map = camkes_io_map;
    c->mapped = NULL;
    mapper->cookie = c;
    mapper->io_map_fn = io_map;
#endif
    mapper->io_unmap_fn = io_unmap;
    return 0;
}

int camkes_io_port_ops(ps_io_port_ops_t *ops) {
    assert(ops != NULL);
    ops->io_port_in_fn = camkes_io_port_in;
    ops->io_port_out_fn = camkes_io_port_out;
    return 0;
}

int
camkes_ps_malloc_ops(ps_malloc_ops_t *ops)
{
    assert(ops != NULL);

    return ps_new_stdlib_malloc_ops(ops);
}

int camkes_io_ops(ps_io_ops_t *ops) {
    assert(ops != NULL);
    return camkes_io_mapper(&ops->io_mapper) ||
           camkes_io_port_ops(&ops->io_port_ops) ||
           camkes_dma_manager(&ops->dma_manager) ||
           camkes_ps_malloc_ops(&ops->malloc_ops);
}
