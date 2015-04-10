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

def check_for_unresolved_references(ast):
    '''
    Check for unresolved references in the AST. Note that this "transformation"
    does not actually modify the AST.
    '''
    for elem in ast:

        # Is this an unresolved reference? Note that we deliberately exclude
        # RPC parameter types and dataport types that are permitted to be
        # unresolved references that will later connect to C typedefs.
        # XXX: Currently Events are also allowed to be unresolved because we
        # infer them at generation time. At some point we should start
        # requiring users to explicitly declare their event types.
        if isinstance(elem, AST.Reference) and elem._referent is None and \
                elem._type not in [AST.Type, AST.Port, AST.Event]:

            raise Exception('%s:%d: unresolved reference to %s' % \
                (elem.filename, elem.lineno, elem._symbol))

        check_for_unresolved_references(elem.children())

    return ast


def check_configuration_for_duplicate_attribute_definitions(conf, defns):
    '''
    Helper function for check_for_duplicate_attribute_definitions. Checks
    whether a given configuration contains multilpe settings with the same
    instance and attribute name, or settings contained in the defns set.

    '''
    if conf is None:
        return

    for setting in conf.settings:
        id = (setting.instance, setting.attribute)
        if id in defns:
            raise Exception('malformed specification: attribute %s.%s ' \
                'is assigned to twice' % id)
        defns.add(id)

def check_for_duplicate_attribute_definitions(ast):
    '''
    Checks for whether an attribute (either declared or undeclared) has been
    assigned to twice in the configuration block. All configuration sections
    appearing in assemblies share a single scope as far as attribute names
    are concerned. Configuration sections in components each have aseparate
    scope.
    '''
    defns = set()
    for assembly in iter_type(ast, AST.Assembly):
        check_configuration_for_duplicate_attribute_definitions(
            assembly.configuration, defns)

    for component in iter_type(ast, AST.Component):
        # defns is cleared to allow different component configurations to have
        # different scopes for attributes
        defns.clear()
        check_configuration_for_duplicate_attribute_definitions(
            component.configuration, defns)

    return ast

PRE_RESOLUTION, POST_RESOLUTION = range(2)

AST_TRANSFORMS = [

    # AST_TRANSFORMS[PRE_RESOLUTION]
    # Transformations that should run before import and reference resolution.
    [
    ],

    # AST_TRANSFORMS[POST_RESOLUTION]
    # Transformations that should run after import and reference resolution.
    [
        check_for_unresolved_references,
        assign_address_spaces,
        check_for_duplicate_attribute_definitions,
    ],

]
