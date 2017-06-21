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

'''Functions relating to collapsing a CAmkES AST procedure into a simpler type.
The purpose of this is to provide template authors with a simpler abstraction
when referencing the 'me' object. CAmkES AST objects typically contain
information that is only relevant in the context of CAmkES.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import camkes.ast as ast

class Parameter(object):
    def __init__(self, name, type, direction):
        self.name = name
        self.type = type
        self.direction = direction

class Method(object):
    def __init__(self, name, return_type, parameters):
        self.name = name
        self.return_type = return_type
        self.parameters = parameters

class Procedure(object):
    def __init__(self, name, methods):
        self.name = name
        self.methods = methods

def simplify_type(t):
    if t is None:
        return None
    assert isinstance(t, ast.Type) or isinstance(t, ast.Reference), \
        'illegal type passed to simplify_type()'
    if isinstance(t, ast.Type):
        return t.type
    return t._symbol

def simplify_parameter(p):
    assert isinstance(p, ast.Parameter), \
        'illegal type passed to simplify_parameter()'
    return Parameter(p.name, simplify_type(p.type), p.direction)

def simplify_method(m):
    assert isinstance(m, ast.Method), \
        'illegal type passed to simplify_method()'
    return Method(m.name, simplify_type(m.return_type),
        [simplify_parameter(p) for p in m.parameters])

def simplify(procedure):
    assert isinstance(procedure, ast.Procedure), \
        'illegal type passed to simplify()'
    return Procedure(procedure.name,
        [simplify_method(m) for m in procedure.methods])
