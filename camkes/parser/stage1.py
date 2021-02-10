#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
Stage 1 parser. The following parser is designed to accept a stage 0 parser,
whose output it consumes. A stage 1 parser makes the following transformation:

    augmented_input ⇒ raw_ast
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import os, plyplus, re
from .base import Parser
from camkes.ast import SourceLocation
from .exception import ParseError

GRAMMAR = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'camkes.g')

_parser = None
def _parse(string):
    # Construct the parser lazily.
    global _parser
    if _parser is None:
        with open(GRAMMAR, 'rt') as f:
            _parser = plyplus.Grammar(f.read())

    # Parse `string` into a plyplus STree.
    return _parser.parse(string)

class Parse1(Parser):
    def __init__(self, parse0):
        self.parse0 = parse0

    def parse_file(self, filename):
        processed, read = self.parse0.parse_file(filename)
        try:
            ast_raw = _parse(processed)
        except plyplus.ParseError as e:
            location = SourceLocation(filename, e, processed)
            e = augment_exception(e)
            raise ParseError(e, location)
        return processed, ast_raw, read

    def parse_string(self, string):
        processed, read = self.parse0.parse_string(string)
        try:
            ast_raw = _parse(processed)
        except plyplus.ParseError as e:
            location = SourceLocation(None, e, processed)
            e = augment_exception(e)
            raise ParseError(e, location)
        return processed, ast_raw, read

def augment_exception(exc):
    '''
    Bolt on some extra, potentially helpful information to a PlyPlus exception.
    There are certain common typos that manifest in inscrutable PlyPlus
    exceptions. This function recognises these and adds a note about the
    possible root cause.
    '''
    assert isinstance(exc, plyplus.ParseError)
    if str(exc) == 'Syntax error in input (details unknown): None\nCould ' \
            'not create parse tree!':
        exc = plyplus.ParseError('%s (missing closing brace?)' % str(exc))
    return exc
