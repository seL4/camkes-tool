/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef _CAMKES_DMA_H_
#define _CAMKES_DMA_H_

#include <platsupport/io.h>
#include <stddef.h>
#include <stdint.h>
#include <utils/util.h>

/* Initialise the DMA allocator. This function must be called before using any
 * of the functions below. Pass in the pool to allocate from, the size of this
 * pool in 4K pages and a function to reverse mappings. Returns 0 on success.
 */
int camkes_dma_init(void *dma_pool, size_t dma_pool_sz,
    uintptr_t (*get_paddr)(void *ptr));

/**
 * Allocate memory to be used for DMA.
 *
 * @param size Size in bytes to allocate
 * @param align Alignment constraint in bytes (0 == none)
 *
 * @return Virtual address of allocation or NULL on failure
 */
void *camkes_dma_alloc(size_t size, int align);

/**
 * Free previously allocated DMA memory.
 *
 * @param ptr Virtual address that was allocated (passing NULL is treated as a
 *    no-op)
 * @param size Size that was given in the allocation request
 */
void camkes_dma_free(void *ptr, size_t size);

/* Return the physical address of a pointer into a DMA buffer. Returns NULL if
 * you pass a pointer into memory that is not part of a DMA buffer. Behaviour
 * is undefined if you pass a pointer into memory that is part of a DMA buffer,
 * but not one currently allocated to you by camkes_dma_alloc_page.
 */
uintptr_t camkes_dma_get_paddr(void *ptr);

/* Initialise a DMA manager for use with libplatsupport. This manager will be
 * backed by the (generated) CAmkES DMA pool. Returns 0 on success.
 *
 * If you only need simple DMA allocation, prefer the alloc_page and free_page
 * functions above, but if you need a more interoperable DMA interface then use
 * this function. Note that you can mix calls to alloc_page, free_page and the
 * manager initialised by this function with no adverse effects.
 */
int camkes_dma_manager(ps_dma_man_t *man);

/* Debug functionality for profiling DMA heap usage. This information is
 * returned from a call to `camkes_dma_stats`. Note that this functionality is
 * only available when NDEBUG is not defined.
 */
typedef struct {

    /* The total size of the heap in bytes. */
    size_t heap_size;

    /* The low water mark of available bytes the heap has ever reached. */
    size_t minimum_heap_size;

    /* The current live (allocated) heap space in bytes. Note that the
     * currently available bytes in the heap can be calculated as
     * `heap_size - current_outstanding`
     */
    size_t current_outstanding;

    /* The number of defragmentation attempts that have been performed. Note
     * that no information is provided as to which of these defragmentation
     * operations did useful work.
     */
    uint64_t defragmentations;

    /* Number of coalescing operations that were performed during
     * defragmentations.
     */
    uint64_t coalesces;

    /* Total number of allocation requests (succeeded or failed) that have been
     * performed.
     */
    uint64_t total_allocations;

    /* Number of allocations that initially failed, but then succeeded on
     * retrying after defragmenting the heap.
     */
    uint64_t succeeded_allocations_on_defrag;

    /* Number of failed allocations. This is separated into those that failed
     * because the heap was exhausted and for some other reason. The total
     * failures is calculable by summing them. The succeeded allocations are
     * available by subtracting their sum from `total_allocations`.
     */
    uint64_t failed_allocations_out_of_memory;
    uint64_t failed_allocations_other;

    /* Average allocation request (succeeded or failed) in bytes. */
    size_t average_allocation;

    /* Minimum allocation request (succeeded or failed) in bytes. */
    size_t minimum_allocation;

    /* Maximum allocation request (succeeded or failed) in bytes. */
    size_t maximum_allocation;

    /* Maximum alignment constraint (succeeded or failed) in bytes. */
    int maximum_alignment;

    /* Minimum alignment constraint (succeeded or failed) in bytes. */
    int minimum_alignment;

} camkes_dma_stats_t;

/* Retrieve the above statistics for the current DMA heap. This function is
 * only provided when NDEBUG is not defined. The caller should not modify or
 * free the returned value that may be a static resource.
 */
const camkes_dma_stats_t *camkes_dma_stats(void);

/* Legacy functionality. Use the general allocation and free functions above in
 * preference to these.
 */
void *camkes_dma_alloc_page(void) DEPRECATED;
void camkes_dma_free_page(void *ptr) DEPRECATED;

#endif
