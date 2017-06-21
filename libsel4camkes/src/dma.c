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

/* CAmkES DMA functionality. Note that parts of this interoperate with
 * generated code to provide complete functionality.
 */

#include <assert.h>
#include <limits.h>
#include <platsupport/io.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <camkes/dma.h>
#include <utils/util.h>
#include <sel4/sel4.h>

/* NOT THREAD SAFE. The code could be made thread safe relatively easily by
 * operating atomically on the free list.
 */

/* We store the free list as a linked-list. If 'head' is NULL that implies we
 * have exhausted our allocation pool.
 */
static void *head;

/* This function will be supplied to us at initialisation of the DMA pool. */
static uintptr_t (*to_paddr)(void *ptr);
static seL4_CPtr (*to_cptr)(void *ptr);

/* A node in the free list. Note that the free list is stored as a linked-list
 * of such nodes *within* the DMA pages themselves. This struct is deliberately
 * arranged to be tightly packed (the non-word sized member at the end) so that
 * it consumes as little size as possible. The size of this struct determines
 * the minimum region we can track, and we'd like to be as permissive as
 * possible. Ordinarily this would be achievable in a straightforward way with
 * `__attribute__((packed, aligned(1)))`, but unaligned accesses to uncached
 * memory (which these will live in) are UNPREDICTABLE on some of our platforms
 * like ARMv7.
 */
typedef struct {

    /* This struct also conceptually has the following member. However, it is
     * not directly necessary because the nodes are stored in-place. The
     * virtual address of a region is available as the pointer to the node
     * itself.
     *
     *  void *vaddr;
     */

    /* The size in bytes of this region. */
    size_t size;

    /* The next node in the list. */
    void *next;

    /* The upper bits of the physical address of this region. We don't need to
     * store the lower bits (the offset into the physical frame) because we can
     * reconstruct these from the offset into the page, obtainable as described
     * above. See `extract_paddr` below.
     */
    uintptr_t paddr_upper:sizeof(uintptr_t) * 8 - PAGE_BITS_4K;

} region_t;

static void save_paddr(region_t *r, uintptr_t paddr) {
    assert(r != NULL);
    r->paddr_upper = paddr >> PAGE_BITS_4K;
}
static uintptr_t PURE try_extract_paddr(region_t *r) {
    assert(r != NULL);
    uintptr_t paddr = r->paddr_upper;
    if (paddr != 0) {
        uintptr_t offset = (uintptr_t)r & MASK(PAGE_BITS_4K);
        paddr = (paddr << PAGE_BITS_4K) | offset;
    }
    return paddr;
}
static uintptr_t extract_paddr(region_t *r) {
    uintptr_t paddr = try_extract_paddr(r);
    if (paddr == 0) {
        /* We've never looked up the physical address of this region. Look it
         * up and cache it now.
         */
        paddr = camkes_dma_get_paddr(r);
        assert(paddr != 0);
        save_paddr(r, paddr);
        paddr = try_extract_paddr(r);
    }
    assert(paddr != 0);
    return paddr;
}

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

        assert(extract_paddr(r) != 0 && "a region includes physical frame 0");

        assert(r->size > 0 && "a region has size 0");

        assert(r->size >= sizeof(region_t) && "a region has an invalid size");

        assert(UINTPTR_MAX - (uintptr_t)r >= r->size &&
            "a region overflows in virtual address space");

        assert(UINTPTR_MAX - extract_paddr(r) >= r->size &&
            "a region overflows in physical address space");
    }

    /* Ensure no regions overlap. */
    for (region_t *r = head; r != NULL; r = r->next) {
        for (region_t *p = head; p != r; p = p->next) {

            uintptr_t r_vaddr UNUSED = (uintptr_t)r,
                      p_vaddr UNUSED = (uintptr_t)p,
                      r_paddr UNUSED = extract_paddr(r),
                      p_paddr UNUSED = extract_paddr(p);

            assert(!((r_vaddr >= p_vaddr && r_vaddr < p_vaddr + p->size) ||
                     (p_vaddr >= r_vaddr && p_vaddr < r_vaddr + r->size)) &&
                "two regions overlap in virtual address space");

            assert(!((r_paddr >= p_paddr && r_paddr < p_paddr + p->size) ||
                     (p_paddr >= r_paddr && p_paddr < r_paddr + r->size)) &&
                "two regions overlap in physical address space");
        }
    }
}

#ifdef NDEBUG
    #define STATS(arg) do { } while (0)
#else
    /* Statistics functionality. */

    #define STATS(arg) do { arg; } while (0)

    static camkes_dma_stats_t stats;

    static size_t total_allocation_bytes;

    const camkes_dma_stats_t *camkes_dma_stats(void) {
        if (stats.total_allocations > 0) {
            stats.average_allocation = total_allocation_bytes / stats.total_allocations;
        } else {
            stats.average_allocation = 0;
        }
        return (const camkes_dma_stats_t*)&stats;
    }
#endif

/* Defragment the free list. Can safely be called at any time. The complexity
 * of this function is at least O(n²).
 *
 * Over time the free list can evolve to contain separate chunks that are
 * actually contiguous, both physically and virtually. This fragmentation can
 * result in unnecessary allocation failures, so this function is provided to
 * coalesce such chunks. For example, the free list may end up like:
 *
 *  ┌─────────────┐   ┌─────────────┐   ┌─────────────┐
 *  │vaddr: 0x4000│   │vaddr: 0x7000│   │vaddr: 0x2000│
 *  │size : 0x1000│   │size : 0x2000│   │size : 0x2000│
 *  │next :       ┼──→│next :       ┼──→│next :   NULL│
 *  │paddr: 0x6000│   │paddr: 0x8000│   │paddr: 0x4000│
 *  └─────────────┘   └─────────────┘   └─────────────┘
 *
 * after defragmentation, the free list will look like:
 *
 *  ┌─────────────┐   ┌─────────────┐
 *  │vaddr: 0x2000│   │vaddr: 0x7000│
 *  │size : 0x3000│   │size : 0x2000│
 *  │next :       ┼──→│next :   NULL│
 *  │paddr: 0x4000│   │paddr: 0x8000│
 *  └─────────────┘   └─────────────┘
 */
static void defrag(void) {
    assert(head != NULL &&
        "attempted defragmentation of DMA free list before initialisation");

    check_consistency();

    STATS(stats.defragmentations++);

    /* For each region in the free list... */
    for (region_t *pprev = NULL, *p = head; p != NULL; pprev = p, p = p->next) {

        uintptr_t p_vstart = (uintptr_t)p,           /* start virtual address */
                  p_vend   = (uintptr_t)p + p->size, /* end virtual address */
                  p_pstart = extract_paddr(p),       /* start physical address */
                  p_pend   = p_pstart + p->size;     /* end physical address */

        /* For each region *before* this one... */
        for (region_t *qprev = NULL, *q = head; q != p; qprev = q, q = q->next) {

            uintptr_t q_vstart = (uintptr_t)q,
                      q_vend   = (uintptr_t)q + q->size,
                      q_pstart = extract_paddr(q),
                      q_pend   = q_pstart + q->size;

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
                STATS(stats.coalesces++);
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
                STATS(stats.coalesces++);

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

int camkes_dma_init(void *dma_pool, size_t dma_pool_sz, size_t page_size,
        uintptr_t (*get_paddr)(void *ptr), seL4_CPtr (*get_cptr)(void *ptr)) {
    /* We should not have already initialised our bookkeeping. */
    assert(head == NULL);

    /* The caller should have passed us a valid DMA pool. */
    if (page_size != 0 && (page_size <= sizeof(region_t) ||
                           (uintptr_t)dma_pool % page_size != 0))  {
        return -1;
    }

    /* Bail out if the caller gave us an insufficiently aligned pool. */
    if (dma_pool == NULL || (uintptr_t)dma_pool % alignof(region_t) != 0) {
        return -1;
    }

    /* We're going to store bookkeeping in the DMA pages, that we expect to be
     * power-of-2-sized, so the bookkeeping struct better be
     * power-of-2-aligned. Your compiler should always guarantee this.
     */
    static_assert(IS_POWER_OF_2(alignof(region_t)),
        "region_t is not power-of-2-aligned");

    /* The page size the caller has given us should be a power of 2 and at least
     * the alignment of `region_t`.
     */
    if (page_size != 0 && (!IS_POWER_OF_2(page_size) ||
                           page_size < alignof(region_t))) {
        return -1;
    }

    to_paddr = get_paddr;
    to_cptr = get_cptr;

    STATS(stats.heap_size = dma_pool_sz);
    STATS(stats.minimum_heap_size = dma_pool_sz);
    STATS(stats.minimum_allocation = SIZE_MAX);
    STATS(stats.minimum_alignment = INT_MAX);

    if (page_size != 0) {
        /* The caller specified a page size. Excellent; we don't have to work
         * it out for ourselves.
         */
        for (void *base = dma_pool; base < dma_pool + dma_pool_sz;
                base += page_size) {
            assert((uintptr_t)base % alignof(region_t) == 0 &&
                "we misaligned the DMA pool base address during "
                "initialisation");
            camkes_dma_free(base, page_size);
        }
    } else {
        /* The lazy caller didn't bother giving us a page size. Manually scan
         * for breaks in physical contiguity.
         */
        for (void *base = dma_pool; base < dma_pool + dma_pool_sz;) {
            uintptr_t base_paddr = get_paddr(base);
            if (base_paddr == 0) {
                /* The caller gave us a region backed by non-reversible frames. */
                return -1;
            }
            void *limit = base + 1;
            uintptr_t next_expected_paddr = base_paddr + 1;
            while (limit < dma_pool + dma_pool_sz) {
                if (limit == NULL) {
                    /* The user gave us a region that wraps virtual memory. */
                    return -1;
                }
                uintptr_t limit_paddr = get_paddr(limit);
                if (limit_paddr == 0) {
                    /* The user gave us a region that wraps physical memory. */
                    return -1;
                }
                if (limit_paddr != next_expected_paddr) {
                    /* We've hit a physical contiguity break (== frame
                     * boundary).
                     */
                    break;
                }
                limit++;
                next_expected_paddr++;
            }
            /* Only add the region if it's large enough to actually contain the
             * necessary metadata.
             */
            if (base + sizeof(region_t) >= limit) {
                assert((uintptr_t)base % alignof(region_t) == 0 &&
                    "we misaligned the DMA pool base address during "
                    "initialisation");
                camkes_dma_free(base, limit - base);
            }

            /* Move to the next region. We always need to be considering a
             * region aligned for bookkeeping, so bump the address up if
             * necessary.
             */
            base = (void*)ALIGN_UP((uintptr_t)limit, alignof(region_t));
        }
    }

    check_consistency();

    return 0;
}

uintptr_t camkes_dma_get_paddr(void *ptr) {
    assert(to_paddr != NULL);
    return to_paddr(ptr);
}

seL4_CPtr camkes_dma_get_cptr(void *ptr) {
    assert(to_cptr != NULL);
    return to_cptr(ptr);
}

/* Allocate a DMA region. This is refactored out of camkes_dma_alloc simply so
 * we can more eloquently express reattempting allocations.
 */
static void *alloc(size_t size, int align) {

    /* Our caller should have rounded 'size' up. */
    assert(size >= sizeof(region_t));

    /* The caller should have ensured 'size' is aligned to the bookkeeping
     * struct, so that the bookkeeping we may have to write for the remainder
     * chunk of a region is aligned.
     */
    assert(size % alignof(region_t) == 0);

    /* The caller should have ensured that the alignment requirements are
     * sufficient that any chunk we ourselves allocate, can later host
     * bookkeeping in its initial bytes when it is freed.
     */
    assert(align >= (int)alignof(region_t));

    /* For each region in the free list... */
    for (region_t *prev = NULL, *p = head; p != NULL; prev = p, p = p->next) {

        if (p->size >= size) {
            /* This region or a subinterval of it may satisfy this request. */

            /* Scan subintervals of 'size' bytes within this region from the
             * end. We scan the region from the end as an optimisation because
             * we can avoid relocating the region's metadata if we find a
             * satisfying allocation that doesn't involve the initial
             * sizeof(region_t) bytes.
             */
            for (void *q = (void*)ROUND_DOWN((uintptr_t)p + p->size - size, align);
                    q == (void*)p || q >= (void*)p + sizeof(region_t);
                    q -= align) {

                if (q + size == (void*)p + p->size ||
                        q + size + sizeof(region_t) <= (void*)p + p->size) {
                    /* Found something that satisfies the caller's
                     * requirements and leaves us enough room to turn the cut
                     * off suffix into a new chunk.
                     */

                    uintptr_t base_paddr = try_extract_paddr(p);

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
                            if (base_paddr != 0) {
                                /* PERF: The original chunk had a physical
                                 * address. Save the overhead of a future
                                 * syscall by reusing this information now.
                                 */
                                save_paddr(r, base_paddr + size);
                            } else {
                                r->paddr_upper = 0;
                            }
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
                        if (base_paddr != 0) {
                            /* PERF: An optimisation as above. */
                            save_paddr(end, base_paddr + start_size + size);
                        } else {
                            end->paddr_upper = 0;
                        }
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

    STATS(({
        stats.total_allocations++;
        if (size < stats.minimum_allocation) {
            stats.minimum_allocation = size;
        }
        if (size > stats.maximum_allocation) {
            stats.maximum_allocation = size;
        }
        if (align < stats.minimum_alignment) {
            stats.minimum_alignment = align;
        }
        if (align > stats.maximum_alignment) {
            stats.maximum_alignment = align;
        }
        total_allocation_bytes += size;
    }));

    if (head == NULL) {
        /* Nothing in the free list. */
        STATS(stats.failed_allocations_out_of_memory++);
        return NULL;
    }

    if (align == 0) {
        /* No alignment requirements. */
        align = 1;
    }

    if (align < (int)alignof(region_t)) {
        /* Allocating something with a weaker alignment constraint than our
         * bookkeeping data may lead to us giving out a chunk of memory that is
         * not sufficiently aligned to host bookkeeping data when it is
         * returned to us. Bump it up in this case.
         */
        align = alignof(region_t);
    }

    if (size < sizeof(region_t)) {
        /* We need to bump up smaller allocations because they may be freed at
         * a point when they cannot be conjoined with another chunk in the heap
         * and therefore need to become host to region_t metadata.
         */
        size = sizeof(region_t);
    }

    if (size % alignof(region_t) != 0) {
        /* We need to ensure that 'size' is aligned to the bookkeeping
         * struct, so that the remainder chunk of a region is aligned.
         */
        size = ROUND_UP(size, alignof(region_t));
    }

    void *p = alloc(size, align);

    if (p == NULL && size > sizeof(region_t)) {
        /* We failed to allocate a matching region, but we may be able to
         * satisfy this allocation by defragmenting the free list and
         * re-attempting.
         */
        defrag();
        p = alloc(size, align);

        if (p != NULL) {
            STATS(stats.succeeded_allocations_on_defrag++);
        }
    }

    check_consistency();

    if (p == NULL) {
        STATS(stats.failed_allocations_other++);
    } else {
        STATS(({
            stats.current_outstanding += size;
            if (stats.heap_size - stats.current_outstanding < stats.minimum_heap_size) {
                stats.minimum_heap_size = stats.heap_size - stats.current_outstanding;
            }
        }));
    }

    return p;
}

void camkes_dma_free(void *ptr, size_t size) {

    /* Allow the user to free NULL. */
    if (ptr == NULL) {
        return;
    }

    /* If the user allocated a region that was too small, we would have rounded
     * up the size during allocation.
     */
    if (size < sizeof(region_t)) {
        size = sizeof(region_t);
    }

    /* The 'size' of all allocated chunk should be aligned to the bookkeeping
     * struct, so bump it to the actual size we have allocated.
     */
    if (size % __alignof__(region_t) != 0) {
        size = ROUND_UP(size, __alignof__(region_t));
    }

    /* We should have never allocated memory that is insufficiently aligned to
     * host bookkeeping data now that it has been returned to us.
     */
    assert((uintptr_t)ptr % alignof(region_t) == 0);

    STATS(({
            if (size >= stats.current_outstanding) {
                stats.current_outstanding = 0;
            } else {
                stats.current_outstanding -= size;
            }
        }));

    region_t *p = ptr;
    p->paddr_upper = 0;
    p->size = size;
    prepend_node(p);

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
