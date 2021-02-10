#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
An example of how to use the AST traversal functionality.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))
import camkes.ast as ast
import camkes.parser as parser

def basic_visit(parent, node, ignored):
    sys.stdout.write(' %s\n' % type(node))
    return ast.TRAVERSAL_RECURSE

def code_gen_enter(parent, node, state):
    if isinstance(node, ast.Method):
        if node.return_type is not None:
            sys.stdout.write(node.return_type)
        else:
            sys.stdout.write('void ')
        sys.stdout.write('%s(' % node.name)
        state['infunction'] = True
        state['firstparameter'] = True
        return ast.TRAVERSAL_RECURSE
    elif isinstance(node, ast.Parameter) and state.get('infunction', False):
        if not state.get('firstparameter', True):
            sys.stdout.write(', ')
        sys.stdout.write('%s %s' % (node.type, node.name))
        state['firstparameter'] = False
        return ast.TRAVERSAL_CONTINUE
    return ast.TRAVERSAL_RECURSE

def code_gen_exit(parent, node, ignored):
    if isinstance(node, ast.Method):
        sys.stdout.write(') {\n  /* hello world */\n}\n')
    return ast.TRAVERSAL_RECURSE

def code_constructor(parent, node, state):
    if not isinstance(node, ast.Parameter) and not isinstance(node, ast.Type):
        state['infunction'] = None

    if isinstance(node, ast.Method):
        if node.name not in state['functions']:
            state['functions'][node.name] = []
            state['infunction'] = node.name
        return ast.TRAVERSAL_RECURSE
    elif isinstance(node, ast.Parameter) or isinstance(node, ast.Type) and state['infunction'] is not None:
        state['functions'][state['infunction']].append(node)
        return ast.TRAVERSAL_CONTINUE
    return ast.TRAVERSAL_RECURSE

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Usage: %s inputfile\n' % sys.argv[0])
        return -1

    with open(sys.argv[1], 'rt') as f:
        s = f.read()

    a = parser.parse_to_ast(s)

    sys.stdout.write('Traverse the AST and print the types of nodes:\n')
    ast.traverse(a, basic_visit, None, None)

    sys.stdout.write('\nNow let\'s try some basic online code generation:\n')
    ast.traverse(a, code_gen_enter, code_gen_exit, {})

    sys.stdout.write('\nHow about the same offline:\n')
    state = {
        'functions':{},
        'infunction':None,
    }
    ast.traverse(a, code_constructor, None, state)
    for k, v in state['functions'].items():
        if v[0] is not None:
            sys.stdout.write(v[0])
        else:
            sys.stdout.write('void ')
        sys.stdout.write('%(name)s(%(params)s) {\n  /* hello world */\n}\n' % {
            'name':k,
            'params':', '.join(map(lambda x: '%s %s' % (x.type, x.name), v[1:])),
        })

    return 0

if __name__ == '__main__':
    sys.exit(main())
