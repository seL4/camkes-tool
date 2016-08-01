#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Hash functions safe for use with persistent caches used by camkes.

This is based on how Python's native hash function
works (at time of writing). We need to deviate from the native
functionality in order to be able to hash lists and deterministically
hash strings.
'''

from camkes.internal.strhash import strhash
import six, types, collections

INITIAL_HASH_VALUE = 0x345678

def hash_extend(current, extra):
    return (current ^ extra) * 1000003

def camkes_hash(value):
    '''
    Hash a value in a manner compatible with camkes' persistant compilation cache:
    - strings are hashed deterministically
    - lists/tuples/dicts are hashed based on their contents
    '''

    # As some types of expected values are intersecting, types are checked in
    # a specific order.

    if isinstance(value, six.string_types):
        # Strings are iterable, but are hashed differently
        # from other iterables.
        return strhash(value)
    elif isinstance(value, (tuple, types.GeneratorType)):
        # Tuples and generators are hashable, so check
        # for them before checking for Hashable as they
        # must be hashed differently.
        return hash_iterable(value)
    elif isinstance(value, collections.Hashable):
        # Some camkes ast objects have a Mapping interface,
        # but are also hashable, and should be hashed normally.
        # This case also catches general hashable types (e.g. int).
        return hash(value)
    elif isinstance(value, collections.Mapping):
        # Dicts and other Mappings that aren't hashable
        return hash_mapping(value)
    elif isinstance(value, collections.Iterable):
        # Lists and other iterables that aren't hashable
        return hash_iterable(value)
    else:
        raise ValueError("Unexpected value: %s" % value)

def hash_iterable(i):
    h = INITIAL_HASH_VALUE
    for v in i:
        h = hash_extend(h, camkes_hash(v))
    return h

def hash_mapping(m):
    h = INITIAL_HASH_VALUE

    keys = m.keys()
    keys.sort()

    for k in keys:
        h = hash_extend(h, strhash(k))
        h = hash_extend(h, camkes_hash(m[k]))
    return h
