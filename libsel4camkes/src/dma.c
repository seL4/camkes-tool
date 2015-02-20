/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* CAmkES DMA functionality. Note that parts of this interoperate with
 * generated code to provide complete functionality.
 */

#include <assert.h>
#include <limits.h>
#include <platsupport/io.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/dma.h>
#include <utils/util.h>

/* NOT THREAD SAFE. The code could be made thread safe relatively easily by
 * operating atomically on the free list.
 */

/* We store the free list as a linked-list. If 'head' is NULL that implies we
 * have exhausted our allocation pool.
 */
static void *head;

/* This function will be supplied to us at initialisation of the DMA pool. */
static uintptr_t (*to_paddr)(void *ptr);

/* A node in the free list. Note that the free list is stored as a linked-list
 * of such nodes *within* the DMA pages themselves.
 */
typedef struct {

    /* This struct also conceptually has the following member. However, it is
     * not directly necessary because the nodes are stored in-place. The
     * virtual address of a region is available as the pointer to the node
     * itself.
     *
     *  void *vaddr;
     */

    /* The physical address of this region. */
    uintptr_t paddr;

    /* The size in bytes of this region. */
    size_t size;

    /* The next node in the list. */
    void *next;

} region_t;

/* Various helpers for dealing with the above data structure layout. */
static void prepend_node(region_t *node) {
    assert(node != NULL);
    node->next = head;
    head = node;
}
static void remove_node(region_t *previous, region_t *node) {
    assert(node != NULL);
    if (previous == NULL) {
        head = node->next;
    } else {
        previous->next = node->next;
    }
}
static void replace_node(region_t *previous, region_t *old, region_t *new) {
    assert(old != NULL);
    assert(new != NULL);
    new->next = old->next;
    if (previous == NULL) {
        head = new;
    } else {
        previous->next = new;
    }
}
static void shrink_node(region_t *node, size_t by) {
    assert(node != NULL);
    assert(by > 0 && node->size > by);
    node->size -= by;
}
static void grow_node(region_t *node, size_t by) {
    assert(node != NULL);
    assert(by > 0);
    node->size += by;
}

/* Check certain assumptions hold on the free list. This function is intended
 * to be a no-op when NDEBUG is defined.
 */
static void check_consistency(void) {
    if (head == NULL) {
        /* Empty free list. */
        return;
    }

    /* Validate that there are no cycles in the free list using Brent's
     * algorithm.
     */
    region_t *tortoise = head, *hare = tortoise->next;
    for (int power = 1, lambda = 1; hare != NULL; lambda++) {
        assert(tortoise != hare && "cycle in free list");
        if (power == lambda) {
            tortoise = hare;
            power *= 2;
            lambda = 0;
        }
        hare = hare->next;
    }

    /* Validate invariants on individual regions. */
    for (region_t *r = head; r != NULL; r = r->next) {

        assert(r != NULL && "a region includes NULL");

        assert(r->paddr != 0 && "a region includes physical frame 0");

        assert((uintptr_t)r % PAGE_SIZE_4K == 0 &&
            "the virtual address of a region is not page-aligned");

        assert(r->paddr % PAGE_SIZE_4K == 0 &&
            "the physical address of a region is not page-aligned");

        assert(r->size % PAGE_SIZE_4K == 0 &&
            "the size of a region is not page-aligned");

        assert(r->size > 0 && "a region has size 0");

        assert(UINTPTR_MAX - (uintptr_t)r >= r->size &&
            "a region overflows in virtual address space");

        assert(UINTPTR_MAX - r->paddr >= r->size &&
            "a region overflows in physical address space");
    }

    /* Ensure no regions overlap. */
    for (region_t *r = head; r != NULL; r = r->next) {
        for (region_t *p = head; p != r; p = p->next) {

            uintptr_t r_vaddr = (uintptr_t)r,
                      p_vaddr = (uintptr_t)p;

            assert(!((r_vaddr >= p_vaddr && r_vaddr < p_vaddr + p->size) ||
                     (p_vaddr >= r_vaddr && p_vaddr < r_vaddr + r->size)) &&
                "two regions overlap in virtual address space");

            assert(!((r->paddr >= p->paddr && r->paddr < p->paddr + p->size) ||
                     (p->paddr >= r->paddr && p->paddr < r->paddr + r->size)) &&
                "two regions overlap in physical address space");
        }
    }
}

/* Defragment the free list. Can safely be called at any time. The complexity
 * of this function is at least O(n^2).
 *
 * Over time the free list can evolve to contain separate chunks that are
 * actually contiguous, both physically and virtually. This fragmentation can
 * result in unnecessary allocation failures, so this function is provided to
 * coalesce such chunks. For example, the free list may end up like:
 *
 *  ┌─────────────┐   ┌─────────────┐   ┌─────────────┐
 *  │vaddr: 0x4000│   │vaddr: 0x7000│   │vaddr: 0x2000│
 *  │paddr: 0x6000│   │paddr: 0x8000│   │paddr: 0x4000│
 *  │size : 0x1000│   │size : 0x2000│   │size : 0x2000│
 *  │next :       ┼──→│next :       ┼──→│next :   NULL│
 *  └─────────────┘   └─────────────┘   └─────────────┘
 *
 * after defragmentation, the free list will look like:
 *
 *  ┌─────────────┐   ┌─────────────┐
 *  │vaddr: 0x2000│   │vaddr: 0x7000│
 *  │paddr: 0x4000│   │paddr: 0x8000│
 *  │size : 0x3000│   │size : 0x2000│
 *  │next :       ┼──→│next :   NULL│
 *  └─────────────┘   └─────────────┘
 */
static void defrag(void) {
    assert(head != NULL &&
        "attempted defragmentation of DMA free list before initialisation");

    check_consistency();

    /* For each region in the free list... */
    for (region_t *pprev = NULL, *p = head; p != NULL; pprev = p, p = p->next) {

        uintptr_t p_vstart = (uintptr_t)p,           /* start virtual address */
                  p_vend   = (uintptr_t)p + p->size, /* end virtual address */
                  p_pstart = p->paddr,               /* start physical address */
                  p_pend   = p->paddr + p->size;     /* end physical address */

        /* For each region *before* this one... */ 
        for (region_t *qprev = NULL, *q = head; q != p; qprev = q, q = q->next) {

            uintptr_t q_vstart = (uintptr_t)q,
                      q_vend   = (uintptr_t)q + q->size,
                      q_pstart = q->paddr,
                      q_pend   = q->paddr + q->size;

            /* We could not have entered this loop if 'p' was the head of the
             * free list.
             */
            assert(pprev != NULL);

            if (p_vstart == q_vend && p_pstart == q_pend) {
                /* 'p' immediately follows the region 'q'. Coalesce 'p' into
                 * 'q'.
                 */
                grow_node(q, p->size);
                remove_node(pprev, p);
                /* Bump the outer scan back to the node we just modified
                 * (accounting for the fact that the next thing we will do is
                 * increment 'p' as we go round the loop). The reason for this
                 * is that our changes may have made further coalescing
                 * possible between the node we modified and where 'p' is
                 * currently pointing.
                 */
                if (qprev == NULL) {
                    /* We just coalesced 'p' into the free list head; reset the
                     * scan. Note that we'll end up skipping the head as we go
                     * round the loop, but that's fine because the body of the
                     * outer loop does nothing for the first iteration.
                     */
                    p = head;
                } else {
                    p = qprev;
                }
                break;
            }

            if (p_vend == q_vstart && p_pend == q_pstart) {
                /* 'p' immediately precedes the region 'q'. Coalesce 'q' into
                 * 'p'.
                 */
                grow_node(p, q->size);
                remove_node(qprev, q);

                /* Similar to above, we bump the outer scan back so we
                 * reconsider 'p' again the next time around the loop. Now that
                 * we've expanded 'p' there may be further coalescing we can
                 * do.
                 */
                p = pprev;
                break;
            }
        }
    }

    check_consistency();
}

int camkes_dma_init(void *dma_pool, size_t dma_pool_sz,
        uintptr_t (*get_paddr)(void *ptr)) {
    /* We should not have already initialised our bookkeeping. */
    assert(head == NULL);

    /* The caller should have passed us a valid DMA pool. */
    if ((uintptr_t)dma_pool % PAGE_SIZE_4K != 0)  {
        return -1;
    }

    to_paddr = get_paddr;

    for (unsigned int i = 0; i < dma_pool_sz; i++) {
        camkes_dma_free(dma_pool + i * PAGE_SIZE_4K, PAGE_SIZE_4K);
    }

    check_consistency();

    return 0;
}

uintptr_t camkes_dma_get_paddr(void *ptr) {
    assert(to_paddr != NULL);
    return to_paddr(ptr);
}

/* Allocate a DMA region. This is refactored out of camkes_dma_alloc simply so
 * we can more eloquently express reattempting allocations.
 */
static void *alloc(size_t size, int align) {

    /* Our caller should have rounded 'size' up. */
    assert(size % PAGE_SIZE_4K == 0);

    /* For each region in the free list... */
    for (region_t *prev = NULL, *p = head; p != NULL; prev = p, p = p->next) {

        if (p->size >= size) {
            /* This region or a subinterval of it may satisfy this request. */

            /* Scan subintervals of 'size' bytes within this region from the
             * end. We scan the region from the end as an optimisation because
             * we can avoid relocating the region's metadata if we find a
             * satisfying allocation that doesn't involve the first page.
             */
            for (void *q = (void*)p + p->size - size; q >= (void*)p;
                    q -= PAGE_SIZE_4K) {

                if (align == 0 || (uintptr_t)q % align == 0) {
                    /* Found something that satisfies the caller's alignment
                     * requirements.
                     */

                    /* There are four possible cases here... */

                    if (p == q) {
                        if (p->size == size) {
                            /* 1. We're giving them the whole chunk; we can
                             * just remove this node.
                             */
                            remove_node(prev, p);
                        } else {
                            /* 2. We're giving them the start of the chunk. We
                             * need to extract the end as a new node.
                             */
                            region_t *r = (void*)p + size;
                            r->paddr = p->paddr + size;
                            r->size = p->size - size;
                            replace_node(prev, p, r);
                        }
                    } else if (q + size == (void*)p + p->size) {
                        /* 3. We're giving them the end of the chunk. We need
                         * to shrink the existing node.
                         */
                        shrink_node(p, size);
                    } else {
                        /* 4. We're giving them the middle of a chunk. We need
                         * to shrink the existing node and extract the end as a
                         * new node.
                         */
                        size_t start_size = (uintptr_t)q - (uintptr_t)p;
                        region_t *end = q + size;
                        end->paddr = p->paddr + start_size + size;
                        end->size = p->size - size - start_size;
                        prepend_node(end);
                        p->size = start_size;
                    }

                    return q;
                }
            }
        }
    }

    /* No satisfying region found. */
    return NULL;
}

void *camkes_dma_alloc(size_t size, int align) {

    if (head == NULL) {
        /* Nothing in the free list. */
        return NULL;
    }

    if (align != 0 && PAGE_SIZE_4K % align != 0 && align % PAGE_SIZE_4K != 0) {
        /* The caller has given us unsatisfiable alignment constraints. */
        return NULL;
    }

    /* PERF: Fast path the allocation of a single page. */
    if (size <= PAGE_SIZE_4K && (align == 0 || PAGE_SIZE_4K % align == 0)) {
        assert(head != NULL);
        region_t *r = head;
        if (r->size > PAGE_SIZE_4K) {
            /* This node contains more than one page. Allocate the caller the
             * last page in order to avoid unnecessary relocation of the
             * metadata out of the first page.
             */
            shrink_node(r, PAGE_SIZE_4K);
            return (void*)r + r->size;
        } else {
            /* This node is only a single page. */
            remove_node(NULL, r);
            return r;
        }
    }

    /* Round up to a page boundary. We allocate entire pages to callers for
     * security because we don't know whether it's safe to collocate other
     * allocations in the same page(s).
     */
    size = ROUND_UP(size, PAGE_SIZE_4K);

    void *p = alloc(size, align);

    if (p == NULL) {
        /* We failed to allocate a matching region, but we may be able to
         * satisfy this allocation by defragmenting the free list and
         * re-attempting.
         */
        defrag();
        p = alloc(size, align);
    }

    check_consistency();

    return p;
}

void camkes_dma_free(void *ptr, size_t size) {
    /* Any pointer we gave out should have been page-aligned. */
    assert(IS_ALIGNED_4K((uintptr_t)ptr));

    /* Allow the user to free NULL. */
    if (ptr == NULL) {
        return;
    }

    uintptr_t paddr = camkes_dma_get_paddr(ptr);
    assert(paddr != 0 && "freeing memory via the DMA allocator that is not "
        "part of the DMA pool");

    /* If the user allocated a region that was not aligned to the page size, we
     * would have rounded up the size during allocation.
     */
    size = ROUND_UP(size, PAGE_SIZE_4K);

    /* PERF: As an optimisation, we see if we can append or prepend this region
     * onto the first node in the free list. This can avoid unnecessary
     * defrag() calls when repeatedly allocating and deallocating the same small
     * chunk.
     */
    region_t *r = head;
    if (r != NULL && ptr + size == r && paddr + size == r->paddr) {
        /* The region being freed precedes the free list head. */
        region_t *p = ptr;
        p->paddr = paddr;
        p->size = size + r->size;
        replace_node(NULL, r, p);
    } else if (r != NULL && (void*)r + r->size == ptr &&
            r->paddr + r->size == paddr) {
        /* The region being freed follows the free list head. */
        grow_node(r, size);
    } else {
        /* Default case. */
        region_t *p = ptr;
        p->paddr = paddr;
        p->size = size;
        prepend_node(p);
    }

    check_consistency();
}

/* The remaining functions are to comply with the ps_io_ops-related interface
 * from libplatsupport. Note that many of the operations are no-ops, because
 * our case is somewhat constrained.
 */

static void *dma_alloc(void *cookie UNUSED, size_t size, int align, int cached,
        ps_mem_flags_t flags UNUSED) {

    /* Ignore the cached argument and allocate an uncached page. The assumption
     * here is that any caller that wants a cached page only wants it so as an
     * optimisation. Their usage pattern is expected to be (1) write repeatedly
     * to the page, (2) flush the page, (3) pass it to a device. In the case of
     * an uncached frame we simply lose some performance in (1) and make (2) a
     * no-op.
     */
    (void)cached;

    return camkes_dma_alloc(size, align);
}

static void dma_free(void *cookie UNUSED, void *addr, size_t size) {
    camkes_dma_free(addr, size);
}

/* All CAmkES DMA pages are pinned for the duration of execution, so this is
 * effectively a no-op.
 */
static uintptr_t dma_pin(void *cookie UNUSED, void *addr, size_t size UNUSED) {
    return camkes_dma_get_paddr(addr);
}

/* As above, all pages are pinned so this is also a no-op. */
static void dma_unpin(void *cookie UNUSED, void *addr UNUSED, size_t size UNUSED) {
}

/* Our whole pool is mapped uncached, so cache ops are irrelevant. */
static void dma_cache_op(void *cookie UNUSED, void *addr UNUSED,
        size_t size UNUSED, dma_cache_op_t op UNUSED) {
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

/* Legacy functions */
void *camkes_dma_alloc_page(void) {
    return camkes_dma_alloc(PAGE_SIZE_4K, PAGE_SIZE_4K);
}
void camkes_dma_free_page(void *ptr) {
    return camkes_dma_free(ptr, PAGE_SIZE_4K);
}
