/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <bits/errno.h>
#include <camkes/tls.h>
#include <sel4utils/arch/util.h>

long sys_set_thread_area(va_list ap) {
#if defined(CONFIG_ARCH_IA32) && defined(CONFIG_KERNEL_STABLE)
    int error;
    uintptr_t p = (uintptr_t)va_arg(ap, uintptr_t);
    error = sel4utils_ia32_tcb_set_tls_base(camkes_get_tls()->tcb_cap, p);
    if (error == seL4_NoError) {
        return 0;
    }
#endif

    /* As part of the initialization of the C library we need to set the
     * thread area (also knows as the TLS base) for thread local storage.
     * As we do not properly support TLS we just ignore this call. Will
     * be fine provided we do not create multiple threads (through libc)
     * or use TLS */
    return 0;
}

long sys_set_tid_address(va_list ap) {
    return -ENOSYS;
}
