/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
    .global _camkes_start
    .extern _camkes_start_c

    .text

_camkes_start:
     b  _camkes_start_c
