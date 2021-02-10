#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Helpers for accessing architecture-specific information
'''

def is_64_bit_arch(arch):
    return arch in ('x86_64', 'aarch64')

def min_untyped_size(arch):
    return 4

def max_untyped_size(arch):
    if is_64_bit_arch(arch):
        return 47
    else:
        return 29
