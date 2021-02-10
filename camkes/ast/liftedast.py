#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import ASTObject
from .objects import Assembly
from .traversal import TraversalAction
import collections

class LiftedAST(ASTObject, collections.Iterable):
    child_fields = ('items',)

    no_hash = ASTObject.no_hash + ('_assembly',)

    def __init__(self, items):
        assert items is None or isinstance(items, (list, tuple))
        super(LiftedAST, self).__init__()
        self._items = list(items or [])
        self._assembly = None
        self.claim_children()

    @property
    def items(self):
        return self._items
    @items.setter
    def items(self, value):
        assert isinstance(value, (list, tuple))
        if self.frozen:
            raise TypeError('you cannot change the items in a frozen lifted '
                'AST')
        self._items = value

    def freeze(self):
        self.items = tuple(self.items)
        super(LiftedAST, self).freeze()

    def claim_children(self):
        [self.adopt(i) for i in self.items]

    @property
    def assembly(self):
        if self._assembly is None:
            for i in self.items:
                if isinstance(i, Assembly):
                    if self.frozen:
                        self._assembly = i
                    return i
        return self._assembly

    def filter(self, function=None):
        if function is None:
            function = lambda x: x is not None
        self.items = [x for x in self.items if function(x)]

    def __iter__(self):
        c = Collector()
        self.postorder(c)
        return iter(c.contents)

class Collector(TraversalAction):
    def __init__(self):
        self.contents = []

    def __call__(self, item):
        self.contents.append(item)
        return item
