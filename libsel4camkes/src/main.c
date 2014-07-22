/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* The entry point for a flattened (single address space) binary. We are
 * expecting to be passed a function pointer of the entry point of the
 * component that we (the current thread) are meant to operate within.
 */
int main(int thread_id, int (*component_main)(int thread_id)) {
    return component_main(thread_id);
}
