#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
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
