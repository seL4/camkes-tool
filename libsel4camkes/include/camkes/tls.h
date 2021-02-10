/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Thread-local storage functionality for CAmkES. */

#include <sel4camkes/gen_config.h>

#include <assert.h>
#include <sel4/sel4.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <utils/util.h>

/* Extend this struct as required. */
typedef struct camkes_tls_t {
    seL4_CPtr tcb_cap;
    seL4_CPtr sc_cap;
    unsigned thread_index;

    /* Cap to our own CNode. May be 0 if we don't have a cap to it. */
    seL4_CPtr cnode_cap;

    /* Members used for lazy saving of reply caps. See the API below for how to
     * interact with these members.
     */
    seL4_CPtr reply_cap_slot;
    bool reply_cap_in_tcb;
    seL4_Error reply_cap_save_error;

} camkes_tls_t;
extern __thread camkes_tls_t camkes_tls;

static inline camkes_tls_t *camkes_get_tls(void)
{
    return &camkes_tls;
}

#ifndef CONFIG_KERNEL_MCS
/** Lazy reply cap save and restore functionality. **/

/**
 * Declare that there is a reply cap currently in your TCB.
 *
 *  @param shadow_slot - An empty CSlot to use as the target for saving the
 *    pending reply cap in future if need be.
 *  @return 0 on success, non-zero on failure.
 *
 * This should be called as soon as possible after receiving a reply cap in
 * order to be safe guarded against further code overwriting the reply cap. The
 * caller needs to pass a slot into which to save this pending reply cap if
 * such a thing needs to be done in the future. Note that we do not support
 * having more than one pending reply cap (saved or otherwise) at once.
 */
int camkes_declare_reply_cap(seL4_CPtr shadow_slot);

/**
 * Save any pending reply cap from accidental deletion.
 *
 * This should be called unconditionally by code that is about to perform an
 * operation that may overwrite a pending reply cap. Note that this function is
 * deliberately designed with no return value indicating success or failure
 * because the caller has no way of responding to this. The reason is that they
 * likely were not the one responsible for declaring the reply cap and they do
 * not know what the consequences of its loss are. This function is idempotent.
 */
void camkes_protect_reply_cap(void);

/**
 * Discard information related to the current reply cap.
 *
 *  @return seL4_NoError on success, or a syscall error value indicating that
 *    the prior save of this reply cap failed.
 *
 * Calls to this function should be paired with calls to
 * `camkes_protect_reply_cap`. However, the two calls are likely performed in
 * unrelated code. Code that needs to conditionally call this function should
 * examine the value of `camkes_get_tls()->reply_cap_in_tcb` to determine
 * whether the reply cap is still in their TCB and this function does not need
 * to be invoked.
 */
seL4_Error camkes_unprotect_reply_cap(void);
#endif
