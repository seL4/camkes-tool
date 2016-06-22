/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <stdarg.h>
#include "syscalls.h"
#include <utils/util.h>

long sys_madvise(va_list ap UNUSED) {
    /* There is no dynamic memory mapping in CAmkES, so there are no relevant actions for the
     * runtime to take based on madvise directives. Thus we silently ignore any such calls.
     */
    return 0;
}
