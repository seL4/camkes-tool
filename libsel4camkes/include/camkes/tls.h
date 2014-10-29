/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef _CAMKES_TLS_H_
#define _CAMKES_TLS_H_

/* Thread-local storage functionality for CAmkES. */

#include <assert.h>
#include <sel4/sel4.h>
#include <stdint.h>
#include <utils/util.h>

/* Extend this struct as required. */
typedef struct camkes_tls_t {
    seL4_CPtr tcb_cap;
    unsigned int thread_index;
} camkes_tls_t;

static inline camkes_tls_t * UNUSED camkes_get_tls(void) {
    /* We store TLS data in the same page as the thread's IPC buffer, but at
     * the start of the page.
     */
    uintptr_t ipc_buffer = (uintptr_t)seL4_GetIPCBuffer();
    /* Normally we would just use MASK here, but the verification C parser
     * doesn't like the GCC extension used in that macro. The following
     * assertion could be checked at compile-time, but then it appears in input
     * to the verification process that causes other problems.
     */
    assert(PAGE_BITS_4K <= 31 && "mask shift is safe");
    uintptr_t tls = ipc_buffer & ~MASK_UNSAFE(PAGE_BITS_4K);

    /* We should have enough room for the TLS data preceding the IPC buffer. */
    assert(ipc_buffer - tls >= sizeof(camkes_tls_t));

    /* We'd better be returning a valid pointer. */
    assert(tls % __alignof__(camkes_tls_t) == 0);

    return (camkes_tls_t*)tls;
}

#endif
