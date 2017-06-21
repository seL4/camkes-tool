#!/usr/bin/env python
# -*- coding: utf-8 -*-

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
Base cache API that implementations are expected to provide.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import abc, six

class Cache(six.with_metaclass(abc.ABCMeta, object)):

    # Inheritors are expected to have specific, custom arguments they want to
    # receive for `load` and `save`.

    @abc.abstractmethod
    def load(self, *args, **kwargs):
        '''
        Load an entry from the cache. Returns `None` on cache miss.
        '''
        raise NotImplementedError

    @abc.abstractmethod
    def save(self, *args, **kwargs):
        '''
        Save an entry to the cache.
        '''
        raise NotImplementedError

    def flush(self):
        '''
        Flush saved results to persistent cache. If inheritors implement a
        write-through cache, they do not need to override this method.
        '''
        pass
