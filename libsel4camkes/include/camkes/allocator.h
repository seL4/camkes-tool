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

#ifndef _CAMKES_ALLOCATOR_H_
#define _CAMKES_ALLOCATOR_H_

#include <sel4/sel4.h>
#include <stdlib.h>

/* Provide a resource to the (initially empty) cap allocator. You are expected
 * to describe the type, CSpace pointer to it and its attributes if relevant.
 * Returns 0 on success.
 */
int camkes_provide(seL4_ObjectType type, seL4_CPtr ptr, size_t size,
    unsigned attributes);

/* Allocate a seL4 object. Flags should be specified as a bitmask of the
 * attributes the caller requires of the object. Returns a pointer to a cap to
 * the object on success or seL4_CapNull on failure.
 */
seL4_CPtr camkes_alloc(seL4_ObjectType type, size_t size, unsigned flags);

/* Free a pointer that was allocated through this interface. Behaviour is
 * undefined if you pass in a pointer that was not allocated by this allocator.
 */
void camkes_free(seL4_CPtr ptr);

#endif
