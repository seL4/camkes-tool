#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

from camkes.ast import Instance, Connection
from camkes.internal.dictutils import Guard
import collections, os

# Base dictionary of templates for instantiation. Note that the top-level keys
# must be strings, while the following levels are either Guards or strings. A
# guard is essentially a parameterised key in the dictionary that is expecting
# to be passed an AST entity.
TEMPLATES = {
    # Platform
    'seL4':{
        # Type
        Guard(lambda x: isinstance(x, Instance)):{
            'source':'component.template.c',
            'header':'component.template.h',
            'simple':'component.simple.c',
            'linker':'linker.lds',
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPC'):{
            # Direction
            'from':{
                # Item
                'source':'seL4RPC-from.template.c',
            },
            'to':{
                'source':'seL4RPC-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPCSimple'): {
            'from':{
                'source':'seL4RPCSimple-from.template.c',
            },
            'to':{
                'source':'seL4RPCSimple-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPCCall'): {
            'from':{
                'source':'seL4RPCCall-from.template.c',
            },
            'to':{
                'source':'seL4RPCCall-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4SharedData'):{
            'from':{
                'source':'seL4SharedData-from.template.c',
            },
            'to':{
                'source':'seL4SharedData-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4Asynch'):{
            'from':{
                'source':'seL4Asynch-from.template.c',
            },
            'to':{
                'source':'seL4Asynch-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4AsynchBind'):{
            'from':{
                'source':'seL4AsynchBind-from.template.c',
            },
            'to':{
                'source':'seL4AsynchBind-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4AsynchSpin'):{
            'from':{
                'source':'seL4Asynch-from.template.c',
            },
            'to':{
                'source':'seL4AsynchSpin-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4AsynchQueue'):{
            'from':{
                'source':'seL4AsynchQueue-from.template.c',
            },
            'to':{
                'source':'seL4AsynchQueue-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4AsynchNative'):{
            'from':{
                'source':'seL4AsynchNative-from.template.c',
            },
            'to':{
                'source':'seL4AsynchNative-to.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareMMIO'):{
            'from':{
                'source':'seL4HardwareMMIO.template.c',
            },
            # Hardware connection does NOT have a "to" template.
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareInterrupt'):{
            # Hardware connection does NOT have a "from" template.
            'to':{
                'source':'seL4HardwareInterrupt.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4IOAPICHardwareInterrupt'):{
            # Hardware connection does NOT have a "from" template.
            'to':{
                'source':'seL4IOAPICHardwareInterrupt.template.c',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4HardwareIOPort'):{
            'from':{
                'source':'seL4HardwareIOPort.template.c',
            },
            # IO port connection does NOT need a "to" template.
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4DirectCall'):{
            'from':{
                'source':'seL4DirectCall-from.template.c',
            },
            'to':{
                'source':'seL4DirectCall-to.template.c',
            },
        },
        'Makefile':'Makefile',
        'capdl':'capdl-spec.cdl',
        'label-mapping':'label-mapping.json',
    },
    'CIMP':{ # Message passing Isabelle formalism
        'base':'cimp-base.thy',
    },
    'architecture-semantics':{ # Isabelle ADL formalism
        'theory':'arch-definitions.thy',
    },
    'autocorres':{ # AutoCorres-based C code proofs
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4AsynchNative'):{
            'to':{
                'theory':'autocorres/AsynchNativeTo.template.thy',
            },
            'from':{
                'theory':'autocorres/AsynchNativeFrom.template.thy',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4SharedData'):{
            'to':{
                'theory':'autocorres/SharedDataTo.template.thy',
            },
            'from':{
                'theory':'autocorres/SharedDataFrom.template.thy',
            },
        },
        Guard(lambda x: isinstance(x, Connection) and x.type.name == 'seL4RPCSimple'):{
            'from':{
                'theory':'autocorres/RPCSimpleFrom.template.thy',
                'unifiedtheory':'autocorres/RPCSimple.template.thy',
                'unifiedbase':'autocorres/RPCSimple_base.template.thy',
            },
            'to':{
                'theory':'autocorres/RPCSimpleTo.template.thy',
            },
        },
    },
    'GraphViz':{
        'graph':'graph.dot',
    },
}
PLATFORMS = TEMPLATES.keys()

class Templates(object):
    def __init__(self, platform, **kwargs):
        assert platform in TEMPLATES
        self.base = TEMPLATES[platform]
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

        # Create a mock connection and then try to locate an existing matching
        # key. We do this to allow the caller to replace one of the built-in
        # templates.
        class FakeConnection(Connection):
            def __init__(self):
                self.type = collections.namedtuple('Type', 'name')(connector_name)
        fc = FakeConnection()
        for key in self.base:
            if isinstance(key, Guard) and key(fc):
                k = key
                break
        else:
            # We didn't find an existing key (expected case) so we need to make
            # a new one.
            k = Guard(lambda x, name=connector_name: isinstance(x, Connection) \
                and x.type.name == name)
            self.base[k] = {}

        # Add the given template.
        d = self.base
        prev = k
        for p in path.split('.'):
            if p not in d[prev]:
                d[prev][p] = {}
            d = d[prev]
            prev = p
        d[prev] = template

    def lookup(self, path, entity=None):
        '''Lookup the given path string (dict key elements separated by '.') in
        the underlying dict, using `entity` to test guards.'''
        atoms = path.split('.')
        remaining = self.base # Current sub-dict we are looking at
        for atom in atoms:
            if not isinstance(remaining, dict):
                # We bottomed out of the dict before consuming all the path
                # elements.
                return None

            # Do I naive lookup first under the assumption that this is fast
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

        if not isinstance(remaining, str):
            # The path terminated at an item that is not a leaf.
            return None

        return remaining
