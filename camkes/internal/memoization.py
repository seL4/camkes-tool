#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Caching infrastructure for function calls. Nothing in here is CAmkES-
specific. Note that this memoization implementation is not complete. If you are
using it, you are expected to understand its limitations.

Code clagged from https://wiki.python.org/moin/PythonDecoratorLibrary#Memoize.
'''

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
