/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <camkes/dataport.h>
#include <platsupport/io.h>

/* Force the _dataport_frames  section to be created even if no modules are defined. */
static USED SECTION("_dataport_frames") struct {} dummy_dataport_frame;
/* Definitions so that we can find the exposed dataport frames */
extern dataport_frame_t __start__dataport_frames[];
extern dataport_frame_t __stop__dataport_frames[];

int camkes_dataport_arch_flush_cache(size_t start_offset, size_t size,
                                     uintptr_t dataport_start, size_t dataport_size,
                                     dma_cache_op_t cache_op);
