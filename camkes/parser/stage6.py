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
Stage 6 parser. The following parser is designed to accept a stage 5 parser,
whose output it consumes. This parser's purpose is to combine multiple assembly
entities into a single top-level assembly.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Transformer
from camkes.ast import Assembly, Composition, Configuration, Group, \
    TraversalAction
from .exception import ParseError

def precondition(ast_lifted):
    '''
    Precondition of this parser. No groups should be present in the AST.
    '''
    return all(not isinstance(x, Group) for x in ast_lifted)

def postcondition(ast_lifted):
    '''
    Postcondition of the stage 6 parser. Only a single assembly should remain.
    '''
    class Post(TraversalAction):
        def __init__(self):
            self.count = 0
        def __call__(self, item):
            if isinstance(item, Assembly):
                self.count += 1
            return item

    p = Post()
    ast_lifted.postorder(p)

    return p.count <= 1

def compose_assemblies(ast):
    assembly = ast.assembly

    if assembly is None:
        raise ParseError('no assembly found in input specification')

    # collect pieces from all assemblies
    for a in [x for x in ast.items if isinstance(x, Assembly) and
            not x is assembly]:

        assembly.composition.instances.extend(a.composition.instances)
        assembly.composition.connections.extend(a.composition.connections)

        if a.configuration is not None:
            assembly.configuration.settings.extend(a.configuration.settings)

    # Ensure AST consistency.
    assembly.composition.claim_children()
    assembly.configuration.claim_children()

    # Remove all other assemblies from AST.
    ast.filter(lambda x: not isinstance(x, Assembly) or x is assembly)

class Parse6(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        compose_assemblies(ast_lifted)
        return ast_lifted, read
