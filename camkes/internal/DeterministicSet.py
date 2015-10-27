#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import collections

class DeterministicSet(collections.MutableSet):
    '''A replica of the native Python set type, designed to be deterministic in
    the order in which it returns its contents. Python's set type has the
    unfortunate property that contained elements are ordered (in the context of
    iteration) based on their hash. For certain types (e.g. str) hash is not
    guaranteed to be stable across executions (see the last note about __hash__
    at http://docs.python.org/dev/reference/datamodel.html#object.__hash__).
    The effect of this is that, when we use a set in a template, the template
    can be rendered differently across different executions of the runner. This
    is undesirable for many reasons.'''

    def __init__(self, iterable=None):
        self._elements = []
        for i in iterable or []:
            self.add(i)

    def add(self, elem):
        if elem not in self._elements:
            self._elements.append(elem)

    def __contains__(self, elem):
        return elem in self._elements

    def discard(self, elem):
        try:
            self._elements.remove(elem)
        except ValueError:
            pass

    def __iter__(self):
        return iter(self._elements)

    def __len__(self):
        return len(self._elements)
