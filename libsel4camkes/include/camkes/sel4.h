/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#pragma once

#include <autoconf.h>
#include <sel4/sel4.h>

/* Contains wrappers of seL4 invocations providing compatibility across
 * different kernel versions */

enum {
#ifdef CONFIG_KERNEL_RT
    CamkesCNodeSaveCaller = CNodeSwapCaller,
#else
    CamkesCNodeSaveCaller = CNodeSaveCaller,
#endif
};

static inline int camkes_cnode_save_caller(seL4_CNode service,
    seL4_Word index, seL4_Uint8 depth) {
#ifdef CONFIG_KERNEL_RT
    return seL4_CNode_SwapCaller(service, index, depth);
#else
    return seL4_CNode_SaveCaller(service, index, depth);
#endif
}
