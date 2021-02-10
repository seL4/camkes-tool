#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Stage 10 parser. The following parser is designed to accept a stage 9 parser,
whose output it consumes. This parser's purpose is to freeze the AST. The
functionality of this parsing stage is mostly within the AST itself.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Transformer
from .exception import ParseError

# Re-use the post-condition of the stage 6 parser as our pre-condition; that
# only a single assembly remains.
from .stage6 import postcondition as precondition

def postcondition(ast_lifted):
    '''
    Post-condition of this stage. That all AST objects are frozen.
    '''
    return all(x is None or x.frozen for x in ast_lifted)

def freeze(ast_lifted):
    ast_lifted.freeze()

    assembly = ast_lifted.assembly
    assert assembly is not None

    if len(assembly.composition.instances) == 0:
        raise ParseError('no instances declared in assembly', assembly.location)

class Parse10(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        freeze(ast_lifted)
        return ast_lifted, read
