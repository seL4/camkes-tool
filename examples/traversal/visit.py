#!/usr/bin/env python
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
An example of how to use the AST traversal functionality.
'''

import os, sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))
import camkes.ast as ast
import camkes.parser as parser

def basic_visit(parent, node, ignored):
    print ' %s' % type(node)
    return ast.TRAVERSAL_RECURSE

def code_gen_enter(parent, node, state):
    if isinstance(node, ast.Method):
        if node.return_type is not None:
            print node.return_type,
        else:
            print 'void ',
        print '%s(' % node.name,
        state['infunction'] = True
        state['firstparameter'] = True
        return ast.TRAVERSAL_RECURSE
    elif isinstance(node, ast.Parameter) and state.get('infunction', False):
        if not state.get('firstparameter', True):
            print ', ',
        print '%s %s' % (node.type, node.name),
        state['firstparameter'] = False
        return ast.TRAVERSAL_CONTINUE
    return ast.TRAVERSAL_RECURSE

def code_gen_exit(parent, node, ignored):
    if isinstance(node, ast.Method):
        print ') {\n  /* hello world */\n}'
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
        print >>sys.stderr, 'Usage: %s inputfile' % sys.argv[0]
        return -1

    with open(sys.argv[1], 'r') as f:
        s = f.read()

    a = parser.parse_to_ast(s)

    print 'Traverse the AST and print the types of nodes:'
    ast.traverse(a, basic_visit, None, None)

    print '\nNow let\'s try some basic online code generation:'
    ast.traverse(a, code_gen_enter, code_gen_exit, {})

    print '\nHow about the same offline:'
    state = {
        'functions':{},
        'infunction':None,
    }
    ast.traverse(a, code_constructor, None, state)
    for k, v in state['functions'].items():
        if v[0] is not None:
            print v[0],
        else:
            print 'void ',
        print '%(name)s(%(params)s) {\n  /* hello world */\n}' % {
            'name':k,
            'params':', '.join(map(lambda x: '%s %s' % (x.type, x.name), v[1:])),
        }

    return 0

if __name__ == '__main__':
    sys.exit(main())
