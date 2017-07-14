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

/* Framework for running experiments related to CNode size calculations.
 *
 * Rather than having a universal, hard coded size for CNodes, CAmkES infers
 * the size of a CNode after doing cap allocation by calculating the minimum
 * size it can be while still fitting its contained caps. This calculation
 * needs to exist in two different places: in Python for the CAmkES
 * implementation and in Isabelle/HOL for the label mapping verification. The
 * Isabelle/HOL version is defined in a non-executable manner because this is
 * more natural, but the Python version obviously needs to be executable. As a
 * result, there can be some doubt that the two always return the same answer.
 *
 * The following program enumerates all valid inputs for both and ensures they
 * match. You can use this as a sandbox for trying out modifications to either
 * algorithm. If you're wondering why this is written in C, this was originally
 * a Python program but did not run at sufficient speed to enumerate all inputs
 * in a reasonable time.
 *
 * To compile:
 *
 *     cc -O3 -W -Wall -Wextra -std=c11 cnode-size-playground.c -lm
 */

#include <assert.h>
#include <math.h>
#include <stdio.h>

/* This function is intended to match the semantics of
 * python-capdl/capdl/Object.py:calculate_cnode_size
 */
static int calculate_cnode_size(int max_slot) {
    assert(max_slot >= 0);
    int s = max_slot;
    if (s < 2)
        s = 2;
    double base = log2((double)s);
    s = (int)floor(base) + 1;
    return s;
}

/* This function is intended to match the semantics of
 * l4v/camkes/cdl-refine/Generator_CAMKES_CDL.thy:cnode_size_bits
 */
static int cnode_size_bits(int max_slot) {
    int s = max_slot;
    if (max_slot < 3)
        s = 3;
    for (int i = 0; i <= 28; i++)
        if (1 << i > s)
            return i;
    return -1;
}

int main(void) {
    for (int i = 0; i < (1 << 28) - 1; i++) {
        int size1 = calculate_cnode_size(i);
        int size2 = cnode_size_bits(i);
        if (size1 != size2) {
            fprintf(stderr, "failed for %d\n"
                            " calculate_cnode_size(%d) == %d\n"
                            " cnode_size_bits(%d) == %d\n",
                i, i, size1, i, size2);
            return -1;
        }
    }
    return 0;
}
