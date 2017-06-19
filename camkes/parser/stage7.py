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
Stage 7 parser. The following parser is designed to accept a stage 6 parser,
whose output it consumes. This parser's purpose is to resolve hierarchical
systems into a flat, top-level assembly.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from .base import Transformer
from .exception import ParseError
from camkes.ast import Assembly, ASTObject, AttributeReference, \
    Component, Composition, Configuration, Consumes, Dataport, Emits, \
    Instance, Interface, Provides, Setting, Uses
import copy, six

# The pre-condition of this stage is simply the post-condition of the previous
# stage; that only a single assembly remains.
from .stage6 import postcondition as precondition

class InterfacePointer(object):
    '''
    A representation of a connection end that we will potentially relabel. See
    usage of this below.
    '''
    def __init__(self, instance, interface):
        assert isinstance(instance, Instance)
        assert isinstance(interface, Interface)
        self.instance = instance
        self.interface = interface

    # We need to implement the following methods to allow `InterfacePointer`s
    # to be stored sensibly in dicts. Note that we just implement equality
    # based on memory addresses because we know precisely how this will be
    # used.
    def __hash__(self):
        return hash(self.instance) ^ hash(self.interface)
    def __eq__(self, other):
        if not isinstance(other, InterfacePointer):
            return False
        return self.instance is other.instance and \
               self.interface is other.interface
    def __ne__(self, other):
        return not self.__eq__(other)

def derive(obj, namespace):
    '''
    Make a copy of the given object, mangling the new object's name such that
    it will not conflict with existing objects.
    '''
    assert isinstance(obj, ASTObject)
    assert namespace is None or isinstance(namespace, six.string_types)
    if namespace is None:
        # No replication necessary.
        return obj
    new = copy.copy(obj)
    if isinstance(new, Setting):
        new.instance = '%s.%s' % (namespace, new.instance)
        if isinstance(new.value, AttributeReference):
            new.value = copy.copy(new.value)
            new.value.reference = '%s.%s' % (namespace, new.value.reference)
    else:
        new.name = '%s.%s' % (namespace, new.name)
        # If this is a component instance, we need to name-mangle its address
        # space as well. If we don't do this, their address space (custom or
        # implicit) can collide with another entity in the hierarchy and users'
        # components can accidentally be combined into a single address space.
        if isinstance(new, Instance):
            new.address_space = '%s.%s' % (namespace, new.address_space)
    return new

def infer_all(item, parent=None):
    '''
    Infer all relevant objects that are direct or indirect children of this
    item. We do this by recursively "hoisting" things from nested compositions
    and configurations. Though the lifted AST has a built-in traversal
    mechanism, we do not use it here because we want to only visit certain
    entities and we want to propagate learned information upwards.
    '''
    assert isinstance(item, (Assembly, Component))
    assert parent is None or isinstance(parent, Instance)

    # A prefix we'll use to name-mangle children of the current item.
    if parent is None:
        prefix = None
    else:
        prefix = parent.name

    # Below we'll discover and then derive two types of instances: our
    # immediate children and indirect children, which will be accumulated in
    # these lists, respectively. We use two separate lists because we want to
    # maintain the ordering of immediate children first.
    immediate_instances = []
    child_instances = []

    # Indirect settings we'll accumulate.
    child_settings = []

    # Final connections and settings we'll return.
    connections = []
    final_settings = []

    # In the context of connections, we may need to adjust their ends based on
    # export statements. Rather than trying to do this as we go, we just track
    # which interfaces are just aliases for others. These will be eventually
    # used by our outermost caller.
    aliases = {}

    if item.composition is not None:

        # As we go through the AST, we'll derive new instances. These will have
        # new names (and addresses), but will potentially be referred to later
        # under their old pointers. We track this derivation in a mapping from
        # old instances to new instances in order to adjust these references.
        derived = {}

        # We'll accumulate indirect child connections here.
        child_connections = []

        for i in item.composition.instances:
            assert i.name is not None, 'unnamed instance in AST (bug in ' \
                'stage 3 parser?)'

            # Hoist everything from this instance.
            insts, conns, alias, settings = infer_all(i.type, i)

            # Name-mangle the instances.
            for i2 in insts:
                n = derive(i2, prefix)
                child_instances.append(n)
                derived[i2] = n
            n = derive(i, prefix)
            immediate_instances.append(n)
            derived[i] = n

            child_connections.extend(conns)

            # Adjust the connection aliases for the name-mangling we just
            # performed.
            for k, v in alias.items():
                assert k.instance in derived
                assert v.instance in derived
                k = InterfacePointer(derived[k.instance], k.interface)
                v = InterfacePointer(derived[v.instance], v.interface)
                aliases[k] = v

            child_settings.extend(settings)

        for c in item.composition.connections + child_connections:

            # Derive and then re-adjust the ends of each connection.
            n = derive(c, prefix)

            from_ends = []
            for f in n.from_ends:
                e = copy.copy(f)
                if e.instance is None:
                    if isinstance(item, Assembly):
                        raise ParseError('top-level connection end with no '
                            'instance', e.location)
                    e.instance = parent
                else:
                    assert e.instance in derived
                    e.instance = derived[e.instance]
                from_ends.append(e)
            n.from_ends = from_ends

            to_ends = []
            for t in n.to_ends:
                e = copy.copy(t)
                if e.instance is None:
                    if isinstance(item, Assembly):
                        raise ParseError('top-level connection end with no '
                            'instance', e.location)
                    e.instance = parent
                else:
                    assert e.instance in derived
                    e.instance = derived[e.instance]
                to_ends.append(e)
            n.to_ends = to_ends

            n.claim_children()
            connections.append(n)

        assert len(item.composition.exports) == 0 or not \
            isinstance(item, Assembly), 'export statement in assembly block ' \
            '(bug in stage 4 parser?)'

        # Accrue any new aliases we have.
        for e in item.composition.exports:
            p = InterfacePointer(parent, e.destination)
            assert e.source_instance in derived
            d = InterfacePointer(derived[e.source_instance], e.source_interface)
            aliases[p] = d

    # Accrue any settings we have.
    for s in (item.configuration.settings if item.configuration is not None
            else []) + child_settings:
        n = derive(s, prefix)
        final_settings.append(n)

    return immediate_instances + child_instances, connections, aliases, \
        final_settings

class Parse7(Transformer):
    def precondition(self, ast_lifted, _):
        return precondition(ast_lifted)

    def postcondition(self, ast_lifted, _):
        '''
        There is no natural post-condition for this transformation because the
        action taken has been to augment the top-level assembly with
        information that still remains in the AST. This could be formulated
        with an expensive and complex traversal, but it is not worth it.
        '''
        return True

    def transform(self, ast_lifted, read):
        assembly = ast_lifted.assembly

        # Hoist everything relevant from the assembly and its children.
        instances, connections, aliases, settings = infer_all(assembly)

        assembly.composition.instances = instances

        # Replace the connections. Now we take into account the interface
        # aliases.
        assembly.composition.connections = []
        for c in connections:
            for e in c.from_ends + c.to_ends:
                p = InterfacePointer(e.instance, e.interface)
                while p in aliases:
                    p = aliases[p]
                e.instance = p.instance
                e.interface = p.interface
            assembly.composition.connections.append(c)

        # Replace the settings.
        assembly.configuration.settings = settings
        assembly.claim_children()
        return ast_lifted, read
