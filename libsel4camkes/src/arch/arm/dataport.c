/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/dataport.h>
#include <camkes/arch/dataport.h>
#include <platsupport/io.h>
#include <sel4/sel4.h>
#include <utils/util.h>

static int sel4_cache_op(seL4_CPtr frame_cap, seL4_Word start, seL4_Word end, dma_cache_op_t cache_op)
{
    switch (cache_op) {
    case DMA_CACHE_OP_CLEAN:
        return seL4_ARM_Page_Clean_Data(frame_cap, start, end);
    case DMA_CACHE_OP_INVALIDATE:
        return seL4_ARM_Page_Invalidate_Data(frame_cap, start, end);
    case DMA_CACHE_OP_CLEAN_INVALIDATE:
        return seL4_ARM_Page_CleanInvalidate_Data(frame_cap, start, end);
    default:
        ZF_LOGF("Invalid cache_op %d", cache_op);
        return -1;
    }
}

int camkes_dataport_arch_flush_cache(size_t start_offset, size_t size,
                                     uintptr_t dataport_start, size_t dataport_size,
                                     dma_cache_op_t cache_op)
{
    if (start_offset >= dataport_size || size > dataport_size || dataport_size - size < start_offset) {
        ZF_LOGE("Specified range is outside the bounds of the dataport");
        return -1;
    }

    size_t current_offset = start_offset;
    size_t end_offset = start_offset + size;

    /* Find the region that we want to flush */
    for (dataport_frame_t *frame = __start__dataport_frames;
         frame < __stop__dataport_frames; frame++) {
        if (frame->vaddr == dataport_start) {
            /* Find the frame that we want to start flushing from */
            size_t page_size_of_region = frame->size;
            dataport_frame_t *curr_frame = frame + (current_offset / page_size_of_region);

            while (current_offset < end_offset) {
                size_t frame_top = MIN(ROUND_UP(current_offset + 1, page_size_of_region), end_offset);
                size_t frame_start_offset = current_offset % page_size_of_region;
                size_t frame_end_offset = ((frame_top - 1) % page_size_of_region);
                int error = sel4_cache_op(curr_frame->cap, frame_start_offset, frame_end_offset, cache_op);
                if (error) {
                    ZF_LOGE("Cache flush syscall returned with error: %d", error);
                    return error;
                }
                current_offset = frame_top;
                curr_frame++;
            }

            /* We've done what we needed to do, no need to keep looping over dataport frames */
            break;
        }
    }

    return 0;
}
