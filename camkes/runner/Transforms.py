#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Transformations to be applied to a parsed CAmkES spec before it is operated
on by the runner. Each transformation should be a function that accepts an AST
(list of AST objects) and returns a possibly modified AST.'''

import camkes.ast as AST

def iter_type(ast, type):
    '''Yield all the elements of a particular type from a given AST. No order
    is guaranteed.'''
    for a in ast:
        if isinstance(a, type):
            yield a
        for c in iter_type(a.children(), type):
            yield c

def assign_address_spaces(ast):
    '''Assign an address space identifier (not an ASID in the kernel sense) to
    each component instance. This is based on the groupings specified. Every
    instance that is not part of a group is assigned to its own address space,
    named the same as itself.'''

    counter = 0
    for c in iter_type(ast, AST.Composition):
        # Find all the groups and assign their children the group name as an
        # address space.
        for g in c.groups:
            if g.name is None:
                # XXX: There's no rigorous check here that this name won't
                # collide with something else.
                g.name = 'unamed_group_%d' % counter
                counter += 1
            for i in g.instances:
                i.address_space = g.name
            # Lift the instances out of the group into the parent composition.
            c.instances += g.instances
        # Delete the groups we just processed.
        c.groups = []

    # Assign any remaining instance without an address space (i.e. those that
    # were not grouped) its own name as an address space.
    for i in iter_type(ast, AST.Instance):
        if i.address_space is None:
            i.address_space = i.name

    return ast

AST_TRANSFORMS = [
    assign_address_spaces,
]
