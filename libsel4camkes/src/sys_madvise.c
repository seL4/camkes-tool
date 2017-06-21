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

#define _BSD_SOURCE /* For MADV_* constants */

#include <camkes/vma.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include <utils/util.h>

/** Determine whether an address range is completely backed by mapped memory.
 *
 * @param addr Range start address
 * @param len Range size in bytes
 * @return true if the range is completely mapped
 */
static PURE bool covered(const void *addr, size_t len) {

    /* The range wraps memory. */
    if (UINTPTR_MAX - (uintptr_t)len < (uintptr_t)addr) {
        return false;
    }

    /* Repeatedly scan the VMAs looking for one covering the starting address. When we find one,
     * bump the starting address and reduce the length then loop, scanning for the new starting
     * address. This is not particularly efficient, but has the advantage of being relatively
     * simple.
     */
    size_t i;
    do {
        for (i = 0; i < camkes_vmas_size; i++) {
            if (camkes_vmas[i].start <= addr && camkes_vmas[i].end > addr) {
                /* Found a VMA covering the current starting address. */
                if (!camkes_vmas[i].read && !camkes_vmas[i].write && !camkes_vmas[i].execute) {
                    /* This VMA represents *unmapped* memory. */
                    return false;
                }
                if (camkes_vmas[i].end - addr > len) {
                    /* This VMA covers the entire remaining range. */
                    return true;
                } else {
                    /* This VMA only covers part of the remaining range. */
                    len -= camkes_vmas[i].end - addr;
                    addr = camkes_vmas[i].end;
                }
                break;
            }
        }
    } while (i != camkes_vmas_size);

    /* If we reach this point, then we did a sweep through the VMAs and failed to find one
     * containing the current starting address.
     */
    return false;
}

static long page_size(void) {
    /* Retrieve the page size the first time we run this function. */
    static long pagesize;
    if (pagesize == 0) {
        pagesize = sysconf(_SC_PAGESIZE);
        if (pagesize <= 0) {
            /* Could not get page size */
            pagesize = 0;
        }
    }
    return pagesize;
}

/* There is no dynamic memory management in CAmkES, so `madvise` is no-op. As a nicety, we implement
 * `madvise` to validate its inputs to give callers a more rational environment.
 */
long camkes_sys_madvise(va_list ap UNUSED) {

    void *addr = va_arg(ap, void*);
    size_t length = va_arg(ap, size_t);
    int advice = va_arg(ap, int);

    /* Page size of our platform. */
    long pagesize = page_size();
    if (pagesize == 0) {
        /* Could not get page size */
        return -EINVAL;
    }

    /* Check address is page-aligned. */
    if ((uintptr_t)addr % (uintptr_t)pagesize != 0) {
        return -EINVAL;
    }

    /* Check length is valid. */
    if (length == 0) {
        return -EINVAL;
    }

    /* Check advice is valid. */
    if (advice != MADV_NORMAL && advice != MADV_SEQUENTIAL && advice != MADV_RANDOM &&
        advice != MADV_WILLNEED && advice != MADV_DONTNEED) {
        return -EINVAL;
    }

    /* Check the range being operated on is entirely mapped memory. */
    if (!covered(addr, length)) {
        return -ENOMEM;
    }

    /* Success. */
    return 0;
}

long camkes_sys_mincore(va_list ap) {

    void *addr = va_arg(ap, void*);
    size_t length = va_arg(ap, size_t);
    unsigned char *vec = va_arg(ap, unsigned char*);

    /* Check addr is valid. */
    long pagesize = page_size();
    if (pagesize == 0) {
        /* Could not get page size */
        return -EINVAL;
    }
    if ((uintptr_t)addr % (uintptr_t)pagesize != 0) {
        return -EINVAL;
    }

    /* Check length is valid. */
    if (UINTPTR_MAX - (uintptr_t)length < (uintptr_t)addr) {
        return -ENOMEM;
    }

    size_t pages = length / pagesize;
    if (length % pagesize != 0) {
        pages++;
    }

    /* Check vec is valid. */
    if (vec == NULL || (uintptr_t)vec + pages * sizeof(unsigned char) < (uintptr_t)vec) {
        return -EFAULT;
    }

    /* Now there are only two possibilities for the range [addr, addr + length):
     *
     *  1. It is entirely mapped memory; or
     *  2. Some part of it is unmapped.
     *
     * In the first case, we know the entire region is paged in as there is no paging in CAmkES
     * systems. The second case is a mincore error.
     */

    if (covered(addr, length)) {
        memset(vec, 1, pages * sizeof(unsigned char));
        return 0;
    } else {
        return -ENOMEM;
    }
}

/** The core logic of the checks for mlock/munlock.
 *
 * Note that on CAmkES mlock* and munlock* are all no-ops. This means that the core logic (this
 * function) is identical. It simply validates the inputs.
 *
 * @param addr Address of region start
 * @param len Size of region in bytes
 * @return 0 on success or an errno value.
 */
static long mlock_internal(const void *addr, size_t len) {

    /* Check for overflow. */
    if ((uintptr_t)addr + len < (uintptr_t)addr) {
        return -EINVAL;
    }

    /* Check addr is page-aligned. */
    long pagesize = page_size();
    if (pagesize == 0) {
        /* Could not get page size */
        return -EINVAL;
    }
    if ((uintptr_t)addr % (uintptr_t)pagesize != 0) {
        return -EINVAL;
    }

    if (covered(addr, len)) {
        return 0;
    } else {
        return -ENOMEM;
    }
}

long camkes_sys_mlock(va_list ap) {

    const void *addr = va_arg(ap, const void*);
    size_t len = va_arg(ap, size_t);

    return mlock_internal(addr, len);
}

long camkes_sys_munlock(va_list ap) {

    const void *addr = va_arg(ap, const void*);
    size_t len = va_arg(ap, size_t);

    return mlock_internal(addr, len);
}

long camkes_sys_mlockall(va_list ap) {

    int flags = va_arg(ap, int);

    if ((flags & ~(MCL_CURRENT|MCL_FUTURE)) != 0) {
        return -EINVAL;
    }

    return 0;
}

long camkes_sys_munlockall(va_list ap UNUSED) {
    return 0;
}
