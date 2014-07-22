#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Functionality related to traversing a CAmkES AST with user-provided functions.'''

from GenericObjects import ASTObject

# Enum used below.
CONTINUE, BREAK, RECURSE = range(3)

def traverse(ast, enter, exit, data, parent=None):
    '''Traverse an AST with user-provided functions. This function is expected
    to be be called with four arguments from user code. 'enter' and 'exit'
    should be functions that take three arguments, a parent node, a current node
    and the 'data' parameter that will be passed into it to keep track of state.
    The functions should return one of the three constants above, indicating how
    the traversal should proceed.
     CONTINUE - Do not recurse into the current node's children, but proceed
       directly to its siblings.
     BREAK - Terminate traversal here.
     RECURSE - Recurse into the current node's children before proceeding to its
       siblings. I.e. proceed with the natural traversal.
    '''

    # Let the user pass None if they don't want to do anything on entry or
    # exit of a node.
    if enter is None:
        def _enter(*args):
            pass
        enter = _enter
    if exit is None:
        def _exit(*args):
            pass
        exit = _exit

    assert callable(enter)
    assert callable(exit)

    if isinstance(ast, ASTObject):
        enter_action = enter(parent, ast, data)
        child_action = None
        if enter_action == RECURSE:
            child_action = traverse(ast.children(), enter, exit, data, ast)
        exit_action = exit(parent, ast, data)
        if BREAK in [enter_action, child_action, exit_action]:
            return BREAK
        return exit_action

    elif isinstance(ast, list):
        for node in ast:
            action = traverse(node, enter, exit, data, parent)
            if action == BREAK:
                return BREAK
        return RECURSE

    raise Exception('ast is neither an ASTObject or a list')
