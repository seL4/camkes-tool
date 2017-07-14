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
Stage 4 parser. The following parser is designed to accept a stage 3 parser,
whose output it consumes. Note that this parser, and all parsers from here on
up consume and return the same type of AST representation. Parsers from this
stage and beyond are defined by their postcondition, which should hold on its
output in isolation and in conjunction with any subset of its previous parsers'
postconditions.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Transformer
from camkes.ast import Assembly, ASTObject, Connection, Group, Instance, \
    Interface, Reference, TraversalAction
from .exception import ParseError
from .scope import ForwardScopingContext, ScopingContext
import itertools

def precondition(ast_lifted):
    '''
    Precondition of this parser.

    All items in the AST should have been lifted into `ASTObject`s.
    '''
    return all(x is None or isinstance(x, ASTObject) for x in ast_lifted)

def postcondition(ast_lifted):
    '''
    Postcondition of the AST returned by the stage 4 parser. No references
    should remain in the AST.
    '''
    return all(not isinstance(x, Reference) for x in ast_lifted)

def resolve(ast_lifted, allow_forward=False):

    class Resolver(TraversalAction):
        def __init__(self, context, assembly_scope, allow_forward):
            self.context = context
            self.assembly_scope = assembly_scope
            self.allow_forward = allow_forward
            self.last_seen = None
        def __call__(self, obj):
            if obj is not None:
                if isinstance(obj, Reference):
                    # This loop is expected to exit on the first iteration in the
                    # normal case where we find the referent. Note that we chain
                    # in the assembly scope to allow cross-assembly references.
                    for referent in itertools.chain(
                            self.context.lookup(obj.name, obj.type),
                            self.assembly_scope.lookup(obj.name, obj.type)):
                        return referent
                    else:
                        # If forward references are allowed, let this resolution
                        # failure silently pass. This is to support connections
                        # that reference the interfaces of component instances
                        # that have not yet been defined. A forward lookup of
                        # such a thing fails at this point because the type of
                        # the instance is still a reference. The extra pass
                        # later will resolve these references.
                        if allow_forward and (obj.type is Instance or \
                                obj.type is Interface):
                            return obj

                        # Try to be helpful and look up symbols the user may have
                        # meant.
                        mistyped = ['%s:%s: %s of type %s' %
                            (m.filename or '<unnamed>', m.lineno, m.name,
                            type(m).__name__) for m in self.context.lookup(obj.name)]
                        if len(mistyped) > 0:
                            extra = '; entities of the same name but incorrect ' \
                                'type: \n %s' % '\n '.join(mistyped)
                        else:
                            extra = ''

                        raise ParseError('unknown reference to \'%s\'%s' %
                            ('.'.join(obj.name), extra), obj.location)

                elif not self.allow_forward:
                    self.context.register(obj)

                    # If this is a child of a top-level composition, add it to
                    # the assembly scope. This permits (backwards) references
                    # from one assembly block to another.
                    if isinstance(obj, (Instance, Group, Connection)) and \
                            obj.parent is not None and \
                            isinstance(obj.parent.parent, Assembly):
                        self.assembly_scope.register(obj)

                # Update the last object we operated on. Note that this
                # tracking is irrelevant unless we are handling forward
                # references
                self.last_seen = obj

            return obj

    assembly_scope = ScopingContext()
    assembly_scope.open()

    if allow_forward:
        ctxt = ForwardScopingContext()
        ctxt.open()

        r = Resolver(ctxt, assembly_scope, allow_forward)
        # Set up the last seen object such that all top-level objects are
        # immediately registered when entering the `with` block below.
        r.last_seen = ast_lifted

        # Note everything in all assemblies. This is to support cross-assembly
        # referenes.
        for assembly in (x for x in ast_lifted.items if isinstance(x, Assembly)):
            [assembly_scope.register(y) for y in assembly.composition.children
                if y is not None and not isinstance(y, Reference)]

        with ctxt(r):
            ast_lifted.preorder(r, ctxt)

        # We now need to do another pass through the AST to resolve connection
        # ends that still contain references because their referent was hidden
        # behind other references in the first pass.
        scope = ScopingContext()
        scope.open()
        for assembly in (x for x in ast_lifted.items if isinstance(x, Assembly)):
            [scope.register(y) for y in assembly.composition.children
                if y is not None and not isinstance(y, Reference)]
        for assembly in (x for x in ast_lifted.items if isinstance(x, Assembly)):
            for c in assembly.composition.connections:
                for end in c.from_ends + c.to_ends:
                    if isinstance(end.instance, Reference):
                        try:
                            end.instance = next(scope.lookup(end.instance.name, end.instance.type))
                        except StopIteration:
                            raise ParseError('unknown reference to \'%s\'' %
                                '.'.join(end.instance.name),
                                end.instance.location)
                    if isinstance(end.interface, Reference):
                        try:
                            end.interface = next(scope.lookup(end.interface.name, end.interface.type))
                        except StopIteration:
                            raise ParseError('unknown reference to \'%s\'' %
                                '.'.join(end.interface.name),
                                end.interface.location)

        # With forward references in play, it is possible for the user to
        # induce cycles in the AST. This will explode in interesting ways in
        # later parsing stages, so we check here for cycles to prevent later
        # stages having to cope with this possibility. Note that it is actually
        # possible to create a cyclic AST programmatically even without forward
        # references, but we assume developers will never do this.
        check_acyclic(ast_lifted)

        # At this point, it's possible that we overzealously let a resolution
        # failure pass in the first pass that was not resolved or detected as
        # an error in the follow on pass. Validate that we really have
        # eradicated all references. Note that this deliberately comes after
        # the acyclicity check to avoid an infinite loop on malformed
        # specifications.
        for obj in ast_lifted:
            if isinstance(obj, Reference):
                raise ParseError('unknown reference to \'%s\'' %
                    '.'.join(obj.name), obj.location)

    else:
        ctxt = ScopingContext()
        ctxt.open()

        r = Resolver(ctxt, assembly_scope, allow_forward)

        ast_lifted.postorder(r, ctxt)

    return ast_lifted

class Parse4(Transformer):
    def __init__(self, subordinate_parser, allow_forward=False):
        assert isinstance(allow_forward, bool)
        super(Parse4, self).__init__(subordinate_parser)
        self.allow_forward = allow_forward

    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        return postcondition(ast_lifted)

    def transform(self, ast_lifted, read):
        return resolve(ast_lifted, self.allow_forward), read

def check_acyclic(obj, path=None):
    if path is None:
        path = []

    if any(x is obj for x in path):
        raise ParseError('AST cycle involving entity %s' %
            (obj.name if hasattr(obj, 'name') else '<unnamed>'), obj.location)

    for c in (x for x in obj.children if x is not None):
        check_acyclic(c, path + [obj])
