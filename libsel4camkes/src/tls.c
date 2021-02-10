/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <assert.h>
#include <camkes/tls.h>
#include <sel4/sel4.h>
#include <stdbool.h>
#include <utils/util.h>

__thread camkes_tls_t camkes_tls;

#ifndef CONFIG_KERNEL_MCS

int camkes_declare_reply_cap(seL4_CPtr shadow_slot)
{
    assert(shadow_slot != 0);

    camkes_tls_t *tls = camkes_get_tls();
    assert(tls != NULL);

    assert(!tls->reply_cap_in_tcb &&
           "reply cap already in TCB when declaring a new pending one");

    /* Note the reply cap's shadow slot for a later save. */
    tls->reply_cap_slot = shadow_slot;
    tls->reply_cap_in_tcb = true;

    return 0;
}

void camkes_protect_reply_cap(void)
{
    camkes_tls_t *tls = camkes_get_tls();
    assert(tls != NULL);

    if (tls->reply_cap_in_tcb) {

        /* Where we're going to save the reply cap. Whomever received the reply
         * cap should have set this up.
         */
        assert(tls->reply_cap_slot != 0 &&
               "invalid reply cap slot (corrupted TLS?)");

        if (tls->cnode_cap == 0) {
            /* We don't have a cap to our CNode! */
            tls->reply_cap_save_error = seL4_InvalidCapability;

        } else {
            /* Save the reply cap and mark it as no longer in the TCB. Note that
             * we leave any errors to be discovered by the original declarer of
             * this reply cap. The reason is that the caller of this function
             * has no knowledge of how to respond to this failure.
             */
            tls->reply_cap_save_error = seL4_CNode_SaveCaller(tls->cnode_cap,
                                                              tls->reply_cap_slot, CONFIG_WORD_SIZE);
        }

        tls->reply_cap_in_tcb = false;
    }
}

seL4_Error camkes_unprotect_reply_cap(void)
{
    camkes_tls_t *tls = camkes_get_tls();
    assert(tls != NULL);

    assert(!tls->reply_cap_in_tcb && "attempt to unprotect reply cap which is "
           "still in TCB");

#ifndef NDEBUG
    /* It is not strictly necessary to blank the reply cap slot because it is
     * technically considered free, but doing so helps catch corrupted TLS
     * regions going forwards.
     */
    tls->reply_cap_slot = 0;
#endif

    return tls->reply_cap_save_error;
}

#endif
