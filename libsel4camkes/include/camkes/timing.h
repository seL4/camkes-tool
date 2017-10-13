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

#ifndef _LIBSEL4CAMKES_TIMING_H_
#define _LIBSEL4CAMKES_TIMING_H_

#include <autoconf.h>
#ifdef CONFIG_CAMKES_CONNECTOR_TIMING

#include <assert.h>
#include <sel4bench/sel4bench.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <utils/util.h>


/* This size is arbitrary. */
#define TIMING_ENTRIES 4096

#define TIMING_DEFS(pref, pts...) \
    static int libsel4camkes_timing_buffer_iteration = -1; \
    static ccnt_t libsel4camkes_timing_buffer[TIMING_ENTRIES]; \
    static char *libsel4camkes_timing_points[] = { \
        pts \
    }; \
    void pref##_timing_get_points(char ***points, size_t *size) { \
        *points = libsel4camkes_timing_points; \
        *size = ARRAY_SIZE(libsel4camkes_timing_points); \
    } \
    uint64_t pref##_timing_get_entry(unsigned iteration, char *point) { \
        assert(iteration * ARRAY_SIZE(libsel4camkes_timing_points) < TIMING_ENTRIES); \
        for (unsigned offset = 0; offset < ARRAY_SIZE(libsel4camkes_timing_points); offset++) { \
            if (!strcmp(libsel4camkes_timing_points[offset], point)) { \
                return (uint64_t)libsel4camkes_timing_buffer[iteration * ARRAY_SIZE(libsel4camkes_timing_points) + offset]; \
            } \
        } \
        /* Named point not found. */ \
        return 0; \
    } \
    void pref##_timing_reset(void) { \
        libsel4camkes_timing_buffer_iteration = -1; \
        memset(libsel4camkes_timing_buffer, 0, sizeof(ccnt_t) * TIMING_ENTRIES); \
    }

#define TIMESTAMP(point) \
    do { \
        static bool noted = false; \
        static int index; \
        if (!noted) { \
            for (index = 0; index < ARRAY_SIZE(libsel4camkes_timing_points); index++) { \
                if (!strcmp(libsel4camkes_timing_points[index], point)) { \
                    break; \
                } \
            } \
            assert(index < ARRAY_SIZE(libsel4camkes_timing_points)); \
            noted = true; \
        } \
        if (index == 0) { \
            sel4bench_init(); \
            libsel4camkes_timing_buffer_iteration++; \
        } \
        if (libsel4camkes_timing_buffer_iteration * ARRAY_SIZE(libsel4camkes_timing_points) + index < TIMING_ENTRIES) { \
            libsel4camkes_timing_buffer[libsel4camkes_timing_buffer_iteration * ARRAY_SIZE(libsel4camkes_timing_points) + index] = sel4bench_get_cycle_count(); \
        } \
    } while (0)

#else

#define TIMING_DEFS(pref, pts...) \
    void pref##timing_get_points(char ***points, size_t *size) { \
        *points = NULL; \
        *size = 0; \
    } \
    uint64_t pref##timing_get_entry(unsigned iteration, char *point) { \
        return 0; \
    } \
    void pref##timing_reset(void) { \
    }

#define TIMESTAMP(point) /* nothing */

#endif

#endif
