#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''Caching infrastructure for function calls. Nothing in here is CAmkES-
specific. Note that this memoization implementation is not complete. If you are
using it, you are expected to understand its limitations.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip
import functools, six

if six.PY3:
    # Python 3 has memoization support in functools.
    assert hasattr(functools, 'lru_cache'), '`functools.lru_cache` ' \
        'unexpectedly missing (unsupported Python 3 minor version?)'
    memoize = functools.lru_cache # pylint: disable=E1101

else:
    # Python 2 has no built-in memoization support, so we need to roll our own.
    # See also https://wiki.python.org/moin/PythonDecoratorLibrary#Memoize.
    class memoized(object):
        '''Decorator. Cache a function's return value each time it is called. If
        called later with the same arguments, the cached value is returned (not
        reevaluated).'''

        def __init__(self, func):
            self.func = func
            self.cache = {}

        def __call__(self, *args, **kwargs):
            key = str(args) + str(kwargs)
            if key not in self.cache:
                self.cache[key] = self.func(*args, **kwargs)
            return self.cache[key]

        def __repr__(self):
            '''Return the function's docstring.'''
            return self.func.__doc__

    def memoize():
        return memoized
