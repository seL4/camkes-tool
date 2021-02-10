#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
When using the parser you might want to extend it, which requires direct access
to the AST. The parser is designed to run either standalone or to be imported
from another python file. This file gives an example of how to do the latter.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

# 1. Include the CAmkES parser module.
import sys
sys.path.append('../..')
import camkes.parser as camkes

from os import curdir

def main():
    # Input text.
    s = 'assembly { composition { component foo bar; } }'
    sys.stdout.write('Input:\n%s\n\n' % s)

    # 2. Translate your input into an AST.
    ast = camkes.parse_to_ast(s)

    # At this point, ast contains a list of objects whose types are defined in
    # Objects.py. If you want to manipulate the AST you will want to import the
    # AST module.

    # 3. If your input contains import statements that refer to other files,
    # you can use resolve_imports to inline and parse these into your ast.
    ast, _ = camkes.resolve_imports(ast, curdir)

    # 4. If your input contains any references these will be present in the AST
    # as objects of type camkes.ast.Reference. For example, in the input in
    # this example the component type 'foo' is a reference to a component
    # definition that is expected to be provided elsewhere. After performing
    # reference resolution there may still be references in the AST. This
    # occurs when your references cannot be resolved. For example, in the input
    # here 'foo' is never actually defined.
    ast = camkes.resolve_references(ast, False)

    # 5. If you want to get the AST in an output format call show(). This
    # accepts the AST itself.
    sys.stdout.write('Output:\n%s\n\n' % camkes.show(ast))

    # 6. Some output printers implement a pretty printing function to format the
    # output in a human-readable way. Access this with pretty().
    sys.stdout.write('Pretty printed:\n%s\n\n' % camkes.pretty(camkes.show(ast)))

    return 0

if __name__ == '__main__':
    sys.exit(main())
