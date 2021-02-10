#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Stage 5 parser. The following parser is designed to accept a stage 4 parser,
whose output it consumes. This parser's purpose is to remove Groups from the
lifted AST, adding their implied information as the address space of component
instances.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Transformer
from camkes.ast import Composition, Group, Instance, Reference, TraversalAction

def precondition(ast_lifted):
    '''
    Precondition of this transformation. At this point, no references should be
    left in the AST.
    '''
    return all(not isinstance(x, Reference) for x in ast_lifted)

def postcondition(ast_lifted):
    '''
    Postcondition of this transformation. Afterwards, no groups should remain
    and every instance should have an assigned address space.
    '''
    return all(not isinstance(x, Group) and
        (not isinstance(x, Instance) or x.address_space is not None) for
        x in ast_lifted)

def collapse_groups(ast_lifted):
    class Collapser(TraversalAction):
        def __init__(self):
            self.counter = 0
        def __call__(self, item):
            if isinstance(item, Composition):
                # Remove the groups which should have all been resolved.
                [item.instances.extend(g.instances) for g in item.groups]
                item.groups = []
                item.claim_children()
            elif isinstance(item, Group):
                # Assign an address space to all instances in this group.
                if item.name is None:
                    name = 'unamed_group_%d' % self.counter
                    self.counter += 1
                else:
                    name = item.name
                for i in item.instances:
                    i.address_space = name
            return item

    c = Collapser()
    ast_lifted.postorder(c)

    return ast_lifted

class Parse5(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        return collapse_groups(ast_lifted), read
