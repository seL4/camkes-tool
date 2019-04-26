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

from camkes.ast import Instance, Connection
from camkes.internal.dictutils import Guard
from .exception import TemplateError
import collections
import os
import re
import six

# Base dictionary of templates for instantiation. Note that the top-level keys
# must be strings, while the following levels are either Guards or strings. A
# guard is essentially a parameterised key in the dictionary that is expecting
# to be passed an AST entity.
TEMPLATES = {
    # Platform
    'seL4': {
        # Type
        Guard(lambda x: isinstance(x, Instance)): {
            'source': 'component.common.c',
            'c_environment_source': 'component.environment.c',
            'cakeml_start_source': 'component.environment.start.cakeml',
            'camkesConstants': 'camkesConstants.sml',
            'cakeml_end_source': 'component.environment.end.cakeml',
            'header': 'component.template.h',
            'simple': 'component.simple.c',
            'rumprun': 'component.rumprun.c',
            'debug': 'component.debug.c',
            'linker': 'linker.lds',
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPC'): {
            # Direction
            'from': {
                # Item
                'source': 'seL4RPC-from.template.c',
            },
            'to': {
                'source': 'seL4RPC-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPCSimple'): {
            'from': {
                'source': 'seL4RPCSimple-from.template.c',
            },
            'to': {
                'source': 'seL4RPCSimple-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name in ['seL4RPCCall', 'seL4RPCCallNoType']): {
            'from': {
                'source': 'seL4RPCCall-from.template.c',
            },
            'to': {
                'source': 'seL4RPCCall-to.template.c',
                'cakeml': 'seL4RPCCall-to.template.cakeml',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4SharedData'): {
            'from': {
                'source': 'seL4SharedData-from.template.c',
            },
            'to': {
                'source': 'seL4SharedData-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4Notification'): {
            'from': {
                'source': 'seL4Notification-from.template.c',
            },
            'to': {
                'source': 'seL4Notification-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4NotificationBind'): {
            'from': {
                'source': 'seL4NotificationBind-from.template.c',
            },
            'to': {
                'source': 'seL4NotificationBind-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4NotificationQueue'): {
            'from': {
                'source': 'seL4NotificationQueue-from.template.c',
            },
            'to': {
                'source': 'seL4NotificationQueue-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4NotificationNative'): {
            'from': {
                'source': 'seL4NotificationNative-from.template.c',
            },
            'to': {
                'source': 'seL4NotificationNative-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareMMIO'): {
            'from': {
                'source': 'seL4HardwareMMIO.template.c',
            },
            # Hardware connection does NOT have a "to" template.
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareInterrupt'): {
            # Hardware connection does NOT have a "from" template.
            'to': {
                'source': 'seL4HardwareInterrupt.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4IOAPICHardwareInterrupt'): {
            # Hardware connection does NOT have a "from" template.
            'to': {
                'source': 'seL4IOAPICHardwareInterrupt.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareIOPort'): {
            'from': {
                'source': 'seL4HardwareIOPort.template.c',
            },
            # IO port connection does NOT need a "to" template.
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4DTBHardware'): {
            'from': {
                'source': 'seL4DTBHardware-from.template.c',
            },
            'to': {
                'source': 'seL4DTBHardware-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4DirectCall'): {
            'from': {
                'source': 'seL4DirectCall-from.template.c',
            },
            'to': {
                'source': 'seL4DirectCall-to.template.c',
            },
        },
        'Makefile': 'Makefile',
        'camkes-gen.cmake': 'camkes-gen.cmake',
        'capdl': 'capdl-spec.cdl',

        # Message passing Isabelle formalism
        'cimp-base': 'cimp-base.thy',
        # Isabelle ADL formalism
        'arch-spec': 'arch-definitions.thy',
        # CapDL generator correspondence proofs
        'cdl-refine': 'cdl-refine.thy',
        # Isabelle ROOT file
        'isabelle-root': 'root.thy',
    },
    'autocorres': {  # AutoCorres-based C code proofs
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4NotificationNative'): {
            'to': {
                'theory': 'autocorres/NotificationNativeTo.template.thy',
            },
            'from': {
                'theory': 'autocorres/NotificationNativeFrom.template.thy',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4SharedData'): {
            'to': {
                'theory': 'autocorres/SharedDataTo.template.thy',
            },
            'from': {
                'theory': 'autocorres/SharedDataFrom.template.thy',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPCSimple'): {
            'from': {
                'theory': 'autocorres/RPCSimpleFrom.template.thy',
                'unifiedtheory': 'autocorres/RPCSimple.template.thy',
                'unifiedbase': 'autocorres/RPCSimple_base.template.thy',
            },
            'to': {
                'theory': 'autocorres/RPCSimpleTo.template.thy',
            },
        },
    },
    'GraphViz': {
        'graph': 'graph.dot',
    },
}
PLATFORMS = list(TEMPLATES.keys())


class Templates(object):
    def __init__(self, platform):
        assert platform in TEMPLATES
        self.base = TEMPLATES[platform]
        self.roots = [os.path.abspath(os.path.dirname(__file__))]

    def add_root(self, root):
        self.roots.insert(0, root)

    def get_roots(self):
        return self.roots

    def add(self, connector, connection):
        '''Add connector-based templates to the lookup dictionary. Note that
        this function is intentionally implemented in such a way to allow you
        to overwrite default templates. This assumes you are adding a template
        related to a connector.'''

        # Short circuit the whole process if the caller gave us no templates.
        if connector.from_template is None and connector.to_template is None:
            return set()

        # Use the provided connection to try to locate an existing matching
        # key. We do this to allow the caller to replace one of the built-in
        # templates.
        for key in self.base:
            if isinstance(key, Guard) and key(connection):
                k = key
                break
        else:
            # We didn't find an existing key (expected case) so we need to make
            # a new one.
            k = Guard(lambda x, name=connector.name: isinstance(x, Connection)
                      and x.type.name == name)
            self.base[k] = {}

        dependencies = set()

        # Add the given template(s).
        intermediate = self.base[k]
        if connector.from_template is not None:
            if 'from' not in intermediate:
                intermediate['from'] = {}
            intermediate['from']['source'] = connector.from_template
        if connector.to_template is not None:
            if 'to' not in intermediate:
                intermediate['to'] = {}
            intermediate['to']['source'] = connector.to_template

    def lookup(self, path, entity=None):
        '''Lookup the given path string (dict key elements separated by '/') in
        the underlying dict, using `entity` to test guards.'''
        atoms = path.split('/')
        remaining = self.base  # Current sub-dict we are looking at
        for atom in atoms:
            if not isinstance(remaining, dict):
                # We bottomed out of the dict before consuming all the path
                # elements.
                return None

            # Do a naive lookup first under the assumption that this is fast
            # and we may match a literal string key.
            next_level = remaining.get(atom)

            if next_level is None:
                # We failed to find a match at this level using a naive lookup.
                # We need to do a more complicated lookup across the guards at
                # this level.
                for key, value in remaining.items():
                    if isinstance(key, Guard) and key(entity):
                        # We found a way forward!
                        next_level = value
                        break
                else:
                    # We failed to find any match for the caller's path.
                    return None
            remaining = next_level

        if not isinstance(remaining, six.string_types):
            # The path terminated at an item that is not a leaf.
            return None

        return remaining
