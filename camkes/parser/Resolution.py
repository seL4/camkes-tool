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
Functionality related to resolving references within the AST. The only entity
in here intended to be exposed is resolve_references. From externally, you
should always omit the context parameter. Note that references may still be
present in the returned AST if they did not resolve.
'''

from camkes.ast import ASTObject, Reference, Instance, Connection, Component

class Context(object):
    def __init__(self):
        self.stack = []

    def new_scope(self):
        self.stack.append([])

    def register(self, obj):
        assert isinstance(obj, ASTObject)
        assert not isinstance(obj, Reference)
        assert len(self.stack) > 0
        self.stack[-1].append(obj)

    def pop_scope(self):
        assert len(self.stack) > 0
        self.stack.pop()

    def resolve(self, ref):
        assert isinstance(ref, Reference)
        for scope in reversed(self.stack):
            for obj in reversed(scope):

                # References should never enter a scope (i.e. you can't have a
                # reference to a reference).
                assert not isinstance(obj, Reference)

                if hasattr(obj, 'name') and obj.name == ref._symbol and \
                        isinstance(obj, ref._type):
                    return obj

        # Searched the entire context and didn't find the referent
        return None

def resolve_references(ast, allow_forward=False, context=None):
    assert isinstance(ast, list)

    if not context:
        context = Context()

    def maybe_resolve(ref):
        assert isinstance(ref, Reference)
        assert not ref._referent
        assert isinstance(ref._symbol, str)
        assert ref._symbol

        referent = context.resolve(ref)
        if referent:
            ref.resolve_to(referent)

    context.new_scope()

    if allow_forward:
        # FIXME: It looks to me like a top-level reference will cause an
        # assertion failure. This should be legal.
        map(context.register, ast)

    for i in ast:

        # Is this an unresolved reference?
        if isinstance(i, Reference) and not i._referent:
            maybe_resolve(i)

        elif isinstance(i, Instance) and \
             not isinstance(i, Reference) and \
             isinstance(i.type, Reference) and \
             not i.type._referent:
            maybe_resolve(i.type)

        elif isinstance(i, Connection):
            # Resolve type (connector) and instances.
            for member in [i.type, i.from_instance, i.to_instance]:
                if isinstance(member, Reference) and not member._referent:
                    maybe_resolve(member)

            # After resolving the type and instances, it's possible that we can
            # now resolve the actual interfaces.

            if isinstance(i.from_interface, Reference) and not i.from_interface._referent:
                if isinstance(i.from_instance, Reference):
                    inst = i.from_instance._referent
                else:
                    assert isinstance(i.from_instance, Instance)
                    inst = i.from_instance
                comp = None
                if inst: # The instance was not an unresolved reference.
                    if isinstance(inst.type, Reference):
                        comp = inst.type._referent
                    else:
                        assert isinstance(inst.type, Component)
                        comp = inst.type
                if comp: # The component was not an unresolved reference.
                    interface = [x for x in (comp.uses + comp.emits + comp.dataports) if x.name == i.from_interface._symbol]
                    if len(interface) == 1:
                        i.from_interface.resolve_to(interface[0])

            # Do the same for the 'to' interface.
            if isinstance(i.to_interface, Reference) and not i.to_interface._referent:
                if isinstance(i.to_instance, Reference):
                    inst = i.to_instance._referent
                else:
                    assert isinstance(i.to_instance, Instance)
                    inst = i.to_instance
                comp = None
                if inst:
                    if isinstance(inst.type, Reference):
                        comp = inst.type._referent
                    else:
                        assert isinstance(inst.type, Component)
                        comp = inst.type
                if comp:
                    interface = [x for x in (comp.provides + comp.consumes + comp.dataports) if x.name == i.to_interface._symbol]
                    if len(interface) == 1:
                        i.to_interface.resolve_to(interface[0])

        if not isinstance(i, Reference):
            # This is a referenceable object
            context.register(i)

        resolve_references(i.children(), allow_forward, context)

    context.pop_scope()

    return ast
