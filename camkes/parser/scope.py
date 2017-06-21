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

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import ASTObject, Instance, Reference, SimpleTraversalContext
from .exception import ParseError
import collections, six

class ScopingContext(SimpleTraversalContext):
    '''
    A global context for managing recursive namespace scopes.

    The primary purpose of this class is for reference resolution. References
    may appear in the AST that consist of a symbol name. From their context and
    the CAmkES grammar, the type of the entity to which they refer can be
    inferred. References with attached type information are present in the
    output of the stage 3 parser, a.k.a. the lifted AST. The stage 4 parser
    uses one of these contexts to replace all such references by resolving them
    to the entities to which they refer.

    Usage of this class can be determined by looking at the stage 4 parser, but
    essentially, once you have constructed one of these, call `open` every time
    you enter a nested scope and `close` every time you leave one. Within a
    scope, `register` can be used to save an AST object by name. `lookup` is
    used to search for an entity by name, optionally limiting to type, in the
    immediate and all containing scopes. The first (deepest) matching entity or
    entities are returned. When you close a scope, all registered entities at
    that level are discarded.
    '''

    def __init__(self):
        self.scopes = []

    def open(self):
        self.scopes.append(collections.defaultdict(dict))

    def close(self):
        assert len(self.scopes) > 0
        self.scopes.pop()

    def register(self, obj):
        assert isinstance(obj, ASTObject)
        assert not isinstance(obj, Reference)
        assert len(self.scopes) > 0
        if not hasattr(obj, 'name') or obj.name is None:
            return
        duplicate = self.scopes[-1][obj.name].get(type(obj))
        if duplicate is not None:
            raise ParseError('duplicate definition of %s \'%s\'; previous '
                'definition was at %s:%s' % (type(obj).__name__, obj.name,
                duplicate.filename or '<unnamed>', duplicate.lineno),
                obj.location)
        self.scopes[-1][obj.name][type(obj)] = obj

    def lookup(self, ref, type=None):
        '''
        Look up a symbol in the current context.

        The caller is expected to provide a list of stems of a qualified
        reference as `ref`. That is, to look up the qualified reference
        'foo.bar.baz', the caller would provide `ref` as ['foo', 'bar', 'baz'].
        The values returned can be filtered by type using the optional `type`
        argument.
        '''
        assert isinstance(ref, list) and len(ref) > 0 and \
            all([isinstance(x, six.string_types) for x in ref])

        # Peel off the root stem.
        head, tail = ref[0], ref[1:]

        # Look backwards through the scopes to ensure we yield inner results
        # before outer results.
        for scope in reversed(self.scopes):
            for candidate in scope[head].values():
                if len(tail) == 0:
                    # Bottomed out resolution of the full reference.
                    if type is None or isinstance(candidate, type):
                        yield candidate
                else:
                    # Construct a scope for the entity we've found and
                    # continue the search, descending into it.
                    inner = within(candidate)
                    for c in inner.lookup(tail, type):
                        if type is None or isinstance(c, type):
                            yield c

    def __enter__(self):
        self.open()

    def __exit__(self, *_):
        self.close()

class ForwardScopingContext(ScopingContext):
    '''
    A scoping context that supports the resolution of forward references.

    Note that this class needs support from the associated traversal action to
    function correctly; namely, the traversal action needs to track the last
    AST object it has seen at any point. It is also likely that any caller will
    want to immediately register all top-level AST objects on creation of this
    context. See the usage in the stage 4 parser for more details.
    '''

    def __call__(self, action):
        '''
        Register all children of the last thing our traversal action saw. This
        is designed to be used in a `with` block. The purpose of registering
        all children is so they can be found in the penultimate scope when
        looked up from the ultimate one.
        '''
        assert hasattr(action, 'last_seen')
        assert isinstance(action.last_seen, ASTObject)
        self.open()
        [self.register(x) for x in action.last_seen.children
            if x is not None and not isinstance(x, Reference)]
        return self

    def __enter__(self):
        # Suppress `__enter__` in our parent which would open another scope.
        pass

def within(item):
    '''
    Construct a scope for resolution within an AST object.
    '''
    assert isinstance(item, ASTObject)

    # Create a new scope.
    scope = ScopingContext()
    scope.open()

    if isinstance(item, Instance):
        # HACK: We want references inside an instance to actually resolve to
        # the children of the *type*, not the instance.
        item = item.type

    # Register all children of this object.
    for f in [x for x in item.child_fields if hasattr(item, x) and
            getattr(item, x) is not None]:
        member = getattr(item, f)
        if isinstance(member, list):
            [scope.register(x) for x in member]
        else:
            scope.register(member)

    return scope
