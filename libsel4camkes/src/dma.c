/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* CAmkES DMA functionality. Note that parts of this interoperates with
 * generated code to provide complete functionality.
 */

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/dma.h>
#include <platsupport/io.h>
#include <utils/util.h>

/* NOT THREAD SAFE. The code could be made thread safe relatively easily by
 * operating atomically on the free list.
 */

/* The pool is assumed to be page-aligned and page-sized, but not necessarily
 * physically contiguous. As a consequence of this, the allocator below is not
 * suitable for allocating regions larger than one page.
 */

/* We store the free list as a linked-list with the pointers to the next node
 * in the first word of each page. If 'head' is NULL that implies we have
 * exhausted our allocation pool.
 */
static void *head;
static uintptr_t (*to_paddr)(void *ptr);

int camkes_dma_init(void *dma_pool, size_t dma_pool_sz,
        uintptr_t (*get_paddr)(void *ptr)) {
    /* We should not have already initialised our bookkeeping. */
    assert(head == NULL);

    /* The caller should have passed us a valid DMA pool. */
    if ((uintptr_t)dma_pool % PAGE_SIZE_4K != 0)  {
        return -1;
    }

    for (unsigned int i = 0; i < dma_pool_sz; i++) {
        camkes_dma_free_page(dma_pool + i * PAGE_SIZE_4K);
    }

    to_paddr = get_paddr;

    return 0;
}

uintptr_t camkes_dma_get_paddr(void *ptr) {
    assert(to_paddr != NULL);
    return to_paddr(ptr);
}

void *camkes_dma_alloc_page(void) {
    if (head != NULL) {
        /* We have a page to give out. Take the head of the free list. */
        void *p = head;
        head = *(void**)head;
        return p;
    } else {
        /* No pages remaining. */
        return NULL;
    }
}

void camkes_dma_free_page(void *ptr) {
    /* Any pointer we gave out should have been page-aligned. */
    assert(IS_ALIGNED_4K((uintptr_t)ptr));

    /* Allow the user to free NULL. */
    if (ptr == NULL) {
        return;
    }

    /* Prepend it to the free list. */
    *(void**)ptr = head;
    head = ptr;
}

/* The remaining functions are to comply with the ps_io_ops-related interface
 * from libplatsupport. Note that many of the operations are no-ops, because
 * our case is somewhat constrained.
 */

static void *dma_alloc(void *cookie UNUSED, size_t size, int align, int cached,
        ps_mem_flags_t flags UNUSED) {
    /* We can only give out pages, so this must suit the caller's requirement.
     */
    if (size > PAGE_SIZE_4K) {
        return NULL;
    }
    if (PAGE_SIZE_4K % align != 0) {
        return NULL;
    }

    /* All the frames backing our DMA pool are uncached. */
    if (cached) {
        return NULL;
    }

    return camkes_dma_alloc_page();
}

static void dma_free(void *cookie UNUSED, void *addr, size_t size UNUSED) {
    camkes_dma_free_page(addr);
}

/* All CAmkES DMA pages are pinned for the duration of execution, so this is
 * effectively a no-op.
 */
static uintptr_t dma_pin(void *cookie UNUSED, void *addr, size_t size) {
    /* Our pool is not physically contiguous, so we cannot claim to pin regions
     * that cross page boundaries.
     */
    if (!SAME_PAGE_4K(addr, addr + size - 1)) {
        return 0;
    }

    return camkes_dma_get_paddr(addr);
}

/* As above, all pages are pinned so this is also a no-op. */
static void dma_unpin(void *cookie UNUSED, void *addr UNUSED, size_t size UNUSED) {
}

/* Our whole pool is mapped uncached, so cache ops are irrelevant. */
static void dma_cache_op(void *cookie UNUSED, void *addr UNUSED, size_t size,
        dma_cache_op_t op UNUSED) {
}

int camkes_dma_manager(ps_dma_man_t *man) {
    assert(man != NULL);
    man->dma_alloc_fn = dma_alloc;
    man->dma_free_fn = dma_free;
    man->dma_pin_fn = dma_pin;
    man->dma_unpin_fn = dma_unpin;
    man->dma_cache_op_fn = dma_cache_op;
    return 0;
}

/* Callers of this function are assumed not to be using the underlying
 * allocation functions above. Note that this function actually returns
 * accessible pointers into what would notionally be the free list if you were
 * using the underlying allocation functions.
 */
static void *io_map(void *cookie UNUSED, uintptr_t paddr, size_t size,
        int cached, ps_mem_flags_t flags UNUSED) {
    assert(paddr != 0);

    /* All the frames backing our pool are uncached. */
    if (cached) {
        return NULL;
    }

    /* We can't "map" anything that crosses a frame boundary. */
    if (!SAME_PAGE_4K(paddr, paddr + size - 1)) {
        return NULL;
    }

    /* We don't track physical addresses, so the only way we can locate the
     * requested frame is to iterate over the (known reversible) mappings we
     * have.
     */
    for (void *v = head; v != NULL; v = *(void**)v) {
        uintptr_t p = camkes_dma_get_paddr(v);
        if (PAGE_ALIGN_4K(p) == PAGE_ALIGN_4K(paddr)) {
            /* We found it! */
            uintptr_t offset = paddr & MASK(PAGE_BITS_4K);
            return (void*)((uintptr_t)v | offset);
        }

    }

    /* We didn't find the matching frame. */
    return NULL;
}

/* We never unmap anything. */
static void io_unmap(void *cookie UNUSED, void *vaddr UNUSED, size_t size UNUSED) {
}

int camkes_io_mapper(ps_io_mapper_t *mapper) {
    assert(mapper != NULL);
    mapper->io_map_fn = io_map;
    mapper->io_unmap_fn = io_unmap;
    return 0;
}

/* Is it worth pointing these to a component's accessible IO ports when these
 * are a legacy feature?
 */
static int io_port_in(void *cookie UNUSED, uint32_t port UNUSED,
        int io_size UNUSED, uint32_t *result UNUSED) {
    assert(!"unimplemented");
    return -1;
}
static int io_port_out(void *cookie UNUSED, uint32_t port UNUSED,
        int io_size UNUSED, uint32_t val UNUSED) {
    assert(!"unimplemented");
    return -1;
}

/* This one is static because we don't really want users directly constructing
 * one of these when its only functionality is stubbed out.
 */
static void io_port_ops(ps_io_port_ops_t *ops) {
    assert(ops != NULL);
    ops->io_port_in_fn = io_port_in;
    ops->io_port_out_fn = io_port_out;
}

int camkes_io_ops(ps_io_ops_t *ops) {
    assert(ops != NULL);
    io_port_ops(&ops->io_port_ops);
    return camkes_dma_manager(&ops->dma_manager) ||
        camkes_io_mapper(&ops->io_mapper);
}
