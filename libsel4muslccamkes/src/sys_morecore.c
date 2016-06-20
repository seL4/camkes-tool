/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* defining _GNU_SOURCE to make certain constants appear in muslc. This is rather hacky */
#define _GNU_SOURCE

#include <autoconf.h>
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <sys/mman.h>
#include <errno.h>
#include <assert.h>

#include <sel4utils/util.h>
#include <utils/util.h>

char *morecore_area = NULL;
size_t morecore_size = 0;
static uintptr_t morecore_base = 0;
static uintptr_t morecore_top = 0;

static long
sys_brk_static(va_list ap)
{
    uintptr_t ret;
    uintptr_t newbrk = va_arg(ap, uintptr_t);

    /*if the newbrk is 0, return the bottom of the heap*/
    if (morecore_base == 0) {
        if (morecore_size == 0) {
            LOG_ERROR("Warning: static morecore size is 0");
        }
        morecore_base = (uintptr_t) morecore_area;
        morecore_top = (uintptr_t) &morecore_area[morecore_size];
    }

    if (!newbrk) {
        ret = morecore_base;
    } else if (newbrk < morecore_top && newbrk > (uintptr_t)&morecore_area[0]) {
        ret = morecore_base = newbrk;
    } else {
        ret = 0;
    }

    return ret;
}

long
sys_brk(va_list ap)
{
    if (morecore_area != NULL) {
        return sys_brk_static(ap);
    } else {
        ZF_LOGE("brk called before morecore_area has been initialised");
        return -ENOSYS;
    }
}


/* Large mallocs will result in muslc calling mmap, so we do a minimal implementation
   here to support that. We make a bunch of assumptions in the process */
static long
sys_mmap2_static(va_list ap)
{
    void *addr UNUSED = va_arg(ap, void*);
    size_t length = va_arg(ap, size_t);
    int prot UNUSED = va_arg(ap, int);
    int flags = va_arg(ap, int);
    int fd UNUSED = va_arg(ap, int);
    off_t offset UNUSED = va_arg(ap, off_t);
    if (flags & MAP_ANONYMOUS) {
        if (length > morecore_top) {
            /* The subtraction we're about to do will underflow. */
            return -ENOMEM;
        }
        /* Steal from the top */
        uintptr_t base = morecore_top - length;
        if (base < morecore_base) {
            return -ENOMEM;
        }
        morecore_top = base;
        return base;
    }
    assert(!"not implemented");
    return -ENOMEM;
}

long
sys_mmap2(va_list ap)
{
    if (morecore_area != NULL) {
        return sys_mmap2_static(ap);
    } else {
        ZF_LOGE("mmap called before morecore_area has been initialised");
        return -ENOSYS;
    }
}

long
sys_mmap(va_list ap)
{
    return sys_mmap2(ap);
}

static long
sys_mremap_static(va_list ap)
{
    assert(!"not implemented");
    return -ENOMEM;
}

long
sys_mremap(va_list ap)
{
    if (morecore_area != NULL) {
        return sys_mremap_static(ap);
    } else {
        ZF_LOGE("mremap called before morecore_area has been initialised");
        return -ENOSYS;
    }
}

long sys_munmap(va_list ap)
{
	assert(!"sys_munmap not implemented");
	return 0;
}
