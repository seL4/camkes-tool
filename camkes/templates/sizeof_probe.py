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
Helpers for invoking a c compiler to determine the size of a type
'''

import os, six, subprocess

def probe_sizeof(type_name, compiler_name, extra_flags):
    '''
    Returns the size in bytes of a c type when compiled with a given compiler
    '''
    (max_size, found) = probe_get_max_size(type_name, compiler_name, extra_flags)
    if found:
        return max_size

    # binary search to find the size of the type
    min_size = 1
    while min_size < max_size:
        mid_size = (max_size + min_size) // 2
        comparison = probe_cmp_sizeof(type_name, mid_size, compiler_name, extra_flags)
        if comparison == 1: # sizeof(type) > mid_size
            min_size = mid_size
        elif comparison == -1: # sizeof(type) < mid_size
            max_size = mid_size
        else: # sizeof(type) == mid_size
            return mid_size

    return min_size

def probe_get_max_size(type_name, compiler_name, extra_flags):
    '''
    Returns the lowest power of 2 greater than or equal to the size of
    a given type in bytes
    '''
    # repeatedly double until we get a size bigger than the type
    size = 1
    while True:
        comparison = probe_cmp_sizeof(type_name, size, compiler_name, extra_flags)
        if comparison == 0: # happened to find the exact size
            return (size, True)
        if comparison == -1: # sizeof(type) < size
            return (size, False)

        size *= 2 # double size and keep trying

def probe_cmp_sizeof(type_name, size, compiler_name, extra_flags):
    '''
    Comparator for c types and sizes
    Returns:
        0 if sizeof(type) == size
        1 if sizeof(type) > size
        -1 if sizeof(type) < size
    '''
    # This test program should fail with an error containing <<GT>> if
    # sizeof(type) > size, an error containing <<LT>> if sizeof(type) < size
    # and should compile with no error if sizeof(type) == size.
    program = '''
        _Static_assert(sizeof(%(type_name)s) <= %(size)d, "<<GT>>");
        _Static_assert(sizeof(%(type_name)s) >= %(size)d, "<<LT>>");
    ''' % { "type_name": type_name, "size": size }

    (success, err) = try_compile(program, compiler_name, extra_flags)

    if success:
        return 0

    if err.find("<<GT>>") != -1:
        return 1
    if err.find("<<LT>>") != -1:
        return -1

    assert False, "Probe program invalid"

def try_compile(program, compiler_name, extra_flags):
    '''
    Invokes a given c compiler on a program specified as a string.
    Returns a tuple (success, error), where "success" is a boolean
    that is True iff the program compiled successfully. If "success"
    is False, "error" will contain the text the compiler sent to its
    standard error.
    '''

    flags = [
        '-c',               # compile only
        '-x', 'c',          # specifies the language as c
        '-',                # read the program from stdin
        '-o', os.devnull,   # throw away the output
    ]

    try:
        p = subprocess.Popen([compiler_name] + flags + extra_flags, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                universal_newlines=True)
    except OSError:
        raise Exception("Compiler not found")

    # compile the program
    _, err = p.communicate(program)

    return (p.returncode == 0, err)
