#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

from camkes.internal.dictutils import combinations, Key
import os

# Base dictionary of templates for instantiation. Note that the top-level keys
# must be strings, while the following levels are Keys that contain a string
# that can contain formatting tokens and an optional guard. See usage below in
# Templates where this dictionary is specialised.
TEMPLATES = {
    # Platform
    'seL4':{
        # Type
        Key('%(instance)s'):{
            'source':'component.template.c',
            'header':'component.template.h',
            'simple':'component.simple.c',
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4RPC'):{
            # Direction
            'from':{
                # Item
                'source':'seL4RPC-from.template.c',
            },
            'to':{
                'source':'seL4RPC-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4RPCSimple'): {
            'from':{
                'source':'seL4RPCSimple-from.template.c',
            },
            'to':{
                'source':'seL4RPCSimple-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4RPCCall'): {
            'from':{
                'source':'seL4RPCCall-from.template.c',
            },
            'to':{
                'source':'seL4RPCCall-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4SharedData'):{
            'from':{
                'source':'seL4SharedData-from.template.c',
            },
            'to':{
                'source':'seL4SharedData-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4Asynch'):{
            'from':{
                'source':'seL4Asynch-from.template.c',
            },
            'to':{
                'source':'seL4Asynch-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4AsynchBind'):{
            'from':{
                'source':'seL4AsynchBind-from.template.c',
            },
            'to':{
                'source':'seL4AsynchBind-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4AsynchSpin'):{
            'from':{
                'source':'seL4Asynch-from.template.c',
            },
            'to':{
                'source':'seL4AsynchSpin-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4AsynchQueue'):{
            'from':{
                'source':'seL4AsynchQueue-from.template.c',
            },
            'to':{
                'source':'seL4AsynchQueue-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4AsynchNative'):{
            'from':{
                'source':'seL4AsynchNative-from.template.c',
            },
            'to':{
                'source':'seL4AsynchNative-to.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4HardwareMMIO'):{
            'from':{
                'source':'seL4HardwareMMIO.template.c',
            },
            # Hardware connection does NOT have a "to" template.
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4HardwareInterrupt'):{
            # Hardware connection does NOT have a "from" template.
            'to':{
                'source':'seL4HardwareInterrupt.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4IOAPICHardwareInterrupt'):{
            # Hardware connection does NOT have a "from" template.
            'to':{
                'source':'seL4IOAPICHardwareInterrupt.template.c',
            },
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4HardwareIOPort'):{
            'from':{
                'source':'seL4HardwareIOPort.template.c',
            },
            # IO port connection does NOT need a "to" template.
        },
        Key('%(connection)s', lambda x: x.type.name == 'seL4DirectCall'):{
            'from':{
                'source':'seL4DirectCall-from.template.c',
            },
            'to':{
                'source':'seL4DirectCall-to.template.c',
            },
        },
        Key('Makefile'):'Makefile',
        Key('capdl'):'capdl-spec.cdl',
        Key('label-mapping'):'label-mapping.json',
    },
    'CIMP':{ # Message passing Isabelle formalism
        Key('base'):'cimp-base.thy',
    },
    'architecture-semantics':{ # Isabelle ADL formalism
        Key('theory'):'arch-definitions.thy',
    },
    'GraphViz':{
        Key('graph'):'graph.dot',
    },
}
PLATFORMS = TEMPLATES.keys()

class Templates(object):
    def __init__(self, platform, **kwargs):
        assert platform in TEMPLATES
        self.base = TEMPLATES[platform]
        self.data = kwargs
        self.roots = [os.path.abspath(os.path.dirname(__file__))]

    def add_root(self, root):
        self.roots.insert(0, root)

    def get_roots(self):
        return self.roots

    def add(self, connector_name, path, template):
        '''Add a template to the lookup dictionary. Note that this function is
        intentionally implemented in such a way to allow you to overwrite
        default templates. This assumes you are adding a template related to a
        connector.'''

        # Find the key matching this connector or create a new one.
        k = None
        # Sheesh, what's a guy got to do to mock a class hierarchy these days?
        class FakeConnection(object):
            def __init__(self):
                class FakeType(object):
                    def __init__(self):
                        self.name = connector_name
                self.type = FakeType()
        fc = FakeConnection()
        for key in self.base:
            if key.matches('%(connection)s', fc):
                k = key
                break
        if not k:
            k = Key('%(connection)s', lambda x, name=connector_name: x.type.name == name)
            self.base[k] = {}

        d = self.base
        prev = k
        for p in path.split('.'):
            q = Key(p)
            if q not in d[prev]:
                d[prev][q] = {}
            d = d[prev]
            prev = q
        d[prev] = template

    def lookup(self, path, entity=None):
        '''Lookup the given path string (dict key elements separated by '.') in
        the underlying dict after specialisation, using `entity` to test the
        guard on each key. If this description makes no sense it will probably
        help to trace the execution of an example lookup.'''
        def find(d, atoms):
            if not atoms:
                return d
            for k, v in d.items():
                if isinstance(k, str):
                    if atoms[0] == k:
                        return find(v, atoms[1:])
                else:
                    for c in combinations(self.data):
                        key = k.specialise(c)
                        if key.matches(atoms[0], entity):
                            return find(v, atoms[1:])
        atoms = path.split('.')
        return find(self.base, atoms)
