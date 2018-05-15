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

'''This code manages the name mangling (and reversal of such) that needs to
happen in the templates and follow-on logic in the runner. E.g. based on the
name of a component instance, we need to construct a name of the control TCB.
The logic for performing that translation and (if necessary) reversing it later
is encapsulated here so it can more easily be modified.

Callers should only import and use the Perspective class. When instantiating
one of these, generally as much information as is known should be provided to
give Perspective the opportunity to spot internal inconsistencies. See the
comments in the class itself for further information.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.internal.dictutils import get_fields
import abc, re, six

class Deriver(six.with_metaclass(abc.ABCMeta, object)):
    '''Logic for constructing one symbol from one or more other symbols. This
    class itself is never intended to be directly instantiated and is probably
    best understood by looking at its inherited children.'''
    @abc.abstractmethod
    def inputs(self):
        raise NotImplementedError
    @abc.abstractmethod
    def output(self):
        raise NotImplementedError
    @abc.abstractmethod
    def derive(self, perspective):
        raise NotImplementedError

class ForwardDeriver(Deriver):
    '''Logic for deriving one symbol from several other symbols by way of
    concatenation, interspersed with other static text.'''
    def __init__(self, format, out):
        self.format = format
        self.out = out
    def inputs(self):
        return get_fields(self.format)
    def output(self):
        return self.out
    def derive(self, perspective):
        return self.format % perspective

class BackwardDeriver(Deriver):
    '''Logic for deriving one symbol from one other symbol by pulling out a
    substring of the input.'''
    def __init__(self, regex, input, out):
        self.regex = re.compile(regex)
        self.input = input
        self.out = out
    def inputs(self):
        return set([self.input])
    def output(self):
        return self.out
    def derive(self, perspective):
        m = self.regex.match(perspective[self.input])
        if m is None:
            return None
        return m.group(1)

# The remaining derivers are for specific symbols (or qualities) that are not
# strings. These each need slightly inflected logic.

class ControlDeriver(Deriver):
    def __init__(self, regex, input):
        self.regex = re.compile(regex)
        self.input = input
    def inputs(self):
        return set([self.input])
    def output(self):
        return 'control'
    def derive(self, perspective):
        return self.regex.match(perspective[self.input]) is not None

class PoolDeriver(Deriver):
    def __init__(self, regex, input):
        self.regex = re.compile(regex)
        self.input = input
    def inputs(self):
        return set([self.input])
    def output(self):
        return 'pool'
    def derive(self, perspective):
        return self.regex.match(perspective[self.input]) is not None

class PoolIndexDeriver(Deriver):
    def __init__(self, regex, input):
        self.regex = re.compile(regex)
        self.input = input
    def inputs(self):
        return set([self.input])
    def output(self):
        return 'pool_index'
    def derive(self, perspective):
        m = self.regex.match(perspective[self.input])
        if m is None:
            return None
        return int(m.group(1))

class FromControlDeriver(ForwardDeriver):
    def derive(self, perspective):
        if not perspective.get('control', False):
            return None
        return self.format % perspective

class DMAFrameIndexDeriver(Deriver):
    def __init__(self, regex, input):
        self.regex = re.compile(regex)
        self.input = input
    def inputs(self):
        return set([self.input])
    def output(self):
        return 'dma_frame_index'
    def derive(self, perspective):
        m = self.regex.match(perspective[self.input])
        if m is None:
            return None
        return int(m.group(1))

class PerThreadDeriver(Deriver):
    def __init__(self, name):
        self.name = name
    def inputs(self):
        return set(('instance', 'interface', 'intra_index'))
    def output(self):
        return self.name
    def derive(self, perspective):
        return '%s_%d_%s_%d_%s_%s' % (
            perspective['instance'],
            len(perspective['instance']),
            perspective['interface'],
            len(perspective['interface']),
            perspective['intra_index'],
            self.name)

class FromControlPerThreadDeriver(Deriver):
    def __init__(self, name):
        self.name = name
    def inputs(self):
        return set(('instance',))
    def output(self):
        return self.name
    def derive(self, perspective):
        if not perspective.get('control', False):
            return None
        return '%s_%d_0_control_%d_%s' % (
            perspective['instance'],
            len(perspective['instance']),
            len('0_control'),
            self.name)

class PerThreadInstanceDeriver(Deriver):
    def __init__(self, name):
        self.name = name
        self.outer = re.compile(r'(?P<remainder>.*)_(?P<len>\d+)_\d{4}_(?P<type>.*)$')
        self.inner = re.compile(r'(?P<instance>.*)_(?P<len>\d+)_$')
    def inputs(self):
        return set((self.name,))
    def output(self):
        return 'instance'
    def derive(self, perspective):
        m = self.outer.match(perspective[self.name])
        if m is None:
            return None
        l = int(m.group('len'))
        assert len(m.group('remainder')) >= l, 'unexpected fault in undoing ' \
            '%s name mangling (name mangling and inverse mismatched?)' % self.name
        assert m.group('type') == self.name, 'unexpected type suffix deriving instance ' \
            'from %s (expected %s, got %s)' % (perspective[self.name], self.name, m.group('type'))
        remainder = m.group('remainder')[:-l]
        m = self.inner.match(remainder)
        if m is None:
            return None
        l = int(m.group('len'))
        assert len(m.group('instance')) == l, 'unexpected fault in undoing ' \
            '%s name mangling (name mangling and inverse mismatched?)' % self.name
        return m.group('instance')

class FromControlPerThreadInstanceDeriver(Deriver):
    def __init__(self, name):
        self.name = name
        self.regex = re.compile(r'(?P<instance>.*)_(?P<instance_len>\d+)'
            r'_0_control_(?P<control_len>\d+)_(?P<type>.*)$')
    def inputs(self):
        return set((self.name,))
    def output(self):
        return 'instance'
    def derive(self, perspective):
        m = self.regex.match(perspective[self.name])
        if m is None:
            return None
        assert m.group('type') == self.name, 'unexpected type suffix deriving instance ' \
            'from %s (expected %s, got %s)' % (perspective[self.name], self.name, m.group('type'))
        control_len = int(m.group('control_len'))
        if control_len != len('0_control'):
            return None
        instance_len = int(m.group('instance_len'))
        if instance_len != len(m.group('instance')):
            return None
        return m.group('instance')

class PerThreadInterfaceDeriver(Deriver):
    def __init__(self, name):
        self.name = name
        self.prefix = re.compile(r'(?P<interface>.*)_(?P<len>\d+)_\d{4}_(?P<type>.*)$')
    def inputs(self):
        return set((self.name,))
    def output(self):
        return 'interface'
    def derive(self, perspective):
        m = self.prefix.match(perspective[self.name])
        if m is None:
            return None
        l = int(m.group('len'))
        assert len(m.group('interface')) >= l, 'unexpected fault in undoing ' \
            '%s name mangling (name mangling and inverse mismatched?)' % self.name
        assert m.group('type') == self.name, 'unexpected type suffix deriving interface ' \
            'from %s (expected %s, got %s)' % (perspective[self.name], self.name, m.group('type'))
        return m.group('interface')[-l:]

class PerThreadIntraindexDeriver(Deriver):
    def __init__(self, name):
        self.name = name
        self.regex = re.compile(r'.*_(?P<intra_index>\d{4})_(?P<type>.*)$')
    def inputs(self):
        return set((self.name,))
    def output(self):
        return 'intra_index'
    def derive(self, perspective):
        m = self.regex.match(perspective[self.name])
        if m is None:
            return None
        assert m.group('type') == self.name, 'unexpected type suffix deriving intra index ' \
            'from %s (expected %s, got %s)' % (perspective[self.name], self.name, m.group('type'))
        return m.group('intra_index')

class ToControlPerThreadDeriver(Deriver):
    def __init__(self, name):
        self.name = name
        self.regex = re.compile(r'.*_0_control_(?P<len>\d+)_(?P<type>.*)$')
    def inputs(self):
        return set((self.name,))
    def output(self):
        return 'control'
    def derive(self, perspective):
        m = self.regex.match(perspective[self.name])
        if m is None:
            return False
        assert m.group('type') == self.name, 'unexpected type suffix deriving control ' \
            'from %s (expected %s, got %s)' % (perspective[self.name], self.name, m.group('type'))
        return int(m.group('len')) == len('0_control')

# Phases.
RUNNER, TEMPLATES, FILTERS = list(range(3))

# Instantiate the derivers to describe how name mangling happens in CAmkES. If
# you want to modify the name mangling scheme, this is the place to do it.
DERIVATIONS = {
    RUNNER:[
        ForwardDeriver('%(group)s_group_bin_pd', 'pd'),
        ForwardDeriver('%(elf_name)s_pd', 'pd'),
        BackwardDeriver(r'(.+)_pd$', 'pd', 'elf_name'),
        BackwardDeriver(r'(.+)_group_bin_pd$', 'pd', 'group'),
        ForwardDeriver('%(group)s_cnode', 'cnode'),
        BackwardDeriver(r'(.+)_cnode$', 'cnode', 'group'),
    ], TEMPLATES:[
        ForwardDeriver('dma_frame_%(dma_frame_index)04d', 'dma_frame_symbol'),
        DMAFrameIndexDeriver(r'dma_frame_([0-9]+)$', 'dma_frame_symbol'),
        ForwardDeriver('_camkes_ipc_buffer_%(safe_instance)s_%(interface)s_%(intra_index)04d', 'ipc_buffer_symbol'),
        FromControlDeriver('_camkes_ipc_buffer_%(safe_instance)s_0_control', 'ipc_buffer_symbol'),
        ControlDeriver(r'_camkes_ipc_buffer_.+_0_control$', 'ipc_buffer_symbol'),
        ForwardDeriver('_camkes_stack_%(safe_instance)s_%(interface)s_%(intra_index)04d', 'stack_symbol'),
        FromControlDeriver('_camkes_stack_%(safe_instance)s_0_control', 'stack_symbol'),
        ControlDeriver(r'_camkes_stack_.+_0_control$', 'stack_symbol'),
        ForwardDeriver('%(to_interface)s_cached', 'hardware_cached'),
        BackwardDeriver(r'^(.+)_cached', 'hardware_cached', 'to_interface'),
        ForwardDeriver('%(group)s_group_bin', 'elf_name'),
        BackwardDeriver(r'(.+)_group_bin', 'elf_name', 'group'),
        ForwardDeriver('camkes_dma_pool', 'dma_pool_symbol'),
        BackwardDeriver(r'.*?\.?([a-zA-Z_]\w*)$', 'instance', 'safe_instance'),
        ControlDeriver(r'_passive$', 'passive_attribute'),
        FromControlDeriver('_passive', 'passive_attribute'),
        ForwardDeriver('%(interface)s_passive', 'passive_attribute'),
        BackwardDeriver(r'([^_].*)_passive$', 'passive_attribute', 'interface'),
    ], FILTERS:[
        PerThreadDeriver('tcb'),
        FromControlPerThreadDeriver('tcb'),
        PerThreadInstanceDeriver('tcb'),
        FromControlPerThreadInstanceDeriver('tcb'),
        PerThreadInterfaceDeriver('tcb'),
        PerThreadIntraindexDeriver('tcb'),
        ToControlPerThreadDeriver('tcb'),
        ForwardDeriver('_camkes_ipc_buffer_%(safe_instance)s_%(interface)s_%(intra_index)s', 'ipc_buffer_symbol'),
        FromControlDeriver('_camkes_ipc_buffer_%(safe_instance)s_0_control', 'ipc_buffer_symbol'),
        ControlDeriver(r'_camkes_ipc_buffer_.+_0_control$', 'ipc_buffer_symbol'),
        ForwardDeriver('_camkes_stack_%(safe_instance)s_%(interface)s_%(intra_index)s', 'stack_symbol'),
        FromControlDeriver('_camkes_stack_%(safe_instance)s_0_control', 'stack_symbol'),
        ControlDeriver(r'_camkes_stack_.+_0_control$', 'stack_symbol'),
        ForwardDeriver(r'camkes %(instance)s _camkes_start', 'entry_symbol'),
        BackwardDeriver(r'camkes ([a-zA-Z_]\w*) _camkes_start$', 'entry_symbol', 'instance'),
        ForwardDeriver('%(group)s_group_bin', 'elf_name'),
        BackwardDeriver(r'(.+)_group_bin', 'elf_name', 'group'),
        PoolDeriver(r'.+_tcb_pool_[0-9]+$', 'tcb'),
        PoolIndexDeriver(r'.+_tcb_pool_([0-9]+)$', 'tcb'),
        ForwardDeriver('%(group)s_group_bin_pd', 'pd'),
        ForwardDeriver('%(elf_name)s_pd', 'pd'),
        BackwardDeriver(r'(.+)_pd$', 'pd', 'elf_name'),
        BackwardDeriver(r'(.+)_group_bin_pd$', 'pd', 'group'),
        ForwardDeriver('%(to_interface)s_cached', 'hardware_cached'),
        BackwardDeriver(r'^(.+)_cached', 'hardware_cached', 'to_interface'),
        ForwardDeriver('camkes %(instance)s_dma_pool', 'dma_pool_symbol'),
        BackwardDeriver(r'camkes (.+)_dma_pool$', 'dma_pool_symbol', 'instance'),
        ForwardDeriver('%(instance)s_dma_frame_%(dma_frame_index)04d', 'dma_frame_symbol'),
        BackwardDeriver(r'(.+)_dma_frame_[0-9]+$', 'dma_frame_symbol', 'instance'),
        DMAFrameIndexDeriver(r'.+_dma_frame_([0-9]+)$', 'dma_frame_symbol'),
        ControlDeriver(r'_priority$', 'priority_attribute'),
        FromControlDeriver('_priority', 'priority_attribute'),
        ForwardDeriver('%(interface)s_priority', 'priority_attribute'),
        BackwardDeriver(r'([a-zA-Z_]\w*)_priority$', 'priority_attribute', 'interface'),
        ControlDeriver(r'_affinity$', 'affinity_attribute'),
        FromControlDeriver('_affinity', 'affinity_attribute'),
        ForwardDeriver('%(interface)s_affinity', 'affinity_attribute'),
        BackwardDeriver(r'([a-zA-Z_]\w*)_affinity$', 'affinity_attribute', 'interface'),
        ControlDeriver(r'_domain$', 'domain_attribute'),
        FromControlDeriver('_domain', 'domain_attribute'),
        ForwardDeriver('%(interface)s_domain', 'domain_attribute'),
        BackwardDeriver(r'([a-zA-Z_]\w*)_domain$', 'domain_attribute', 'interface'),
        ForwardDeriver('%(group)s_cnode', 'cnode'),
        BackwardDeriver(r'(.+)_cnode$', 'cnode', 'group'),
        BackwardDeriver(r'.*?\.?([a-zA-Z_]\w*)$', 'instance', 'safe_instance'),
        PerThreadDeriver('sc'),
        FromControlPerThreadDeriver('sc'),
        PerThreadInstanceDeriver('sc'),
        FromControlPerThreadInstanceDeriver('sc'),
        PerThreadInterfaceDeriver('sc'),
        PerThreadIntraindexDeriver('sc'),
        ToControlPerThreadDeriver('sc'),
        FromControlPerThreadInstanceDeriver('passive_init_sc'),
        FromControlPerThreadDeriver('passive_init_sc'),
        ToControlPerThreadDeriver('passive_init_sc'),
        ControlDeriver(r'^_max_priority$', 'max_priority_attribute'),
        FromControlDeriver('_max_priority', 'max_priority_attribute'),
        ForwardDeriver('%(interface)s_max_priority', 'max_priority_attribute'),
        BackwardDeriver(r'^([^_].*)_max_priority$', 'max_priority_attribute', 'interface'),
        ControlDeriver(r'^_period$', 'period_attribute'),
        FromControlDeriver('_period', 'period_attribute'),
        ForwardDeriver('%(interface)s_period', 'period_attribute'),
        BackwardDeriver(r'^([^_].*)_period$', 'period_attribute', 'interface'),
        ControlDeriver(r'^_budget$', 'budget_attribute'),
        FromControlDeriver('_budget', 'budget_attribute'),
        ForwardDeriver('%(interface)s_budget', 'budget_attribute'),
        BackwardDeriver(r'^([^_].*)_budget$', 'budget_attribute', 'interface'),
        ControlDeriver(r'^_data$', 'data_attribute'),
        FromControlDeriver('_data', 'data_attribute'),
        ForwardDeriver('%(interface)s_data', 'data_attribute'),
        BackwardDeriver(r'^([^_].*)_data$', 'data_attribute', 'interface'),
        ControlDeriver(r'^_sc_size_bits$', 'size_bits_attribute'),
        FromControlDeriver('_sc_size_bits', 'size_bits_attribute'),
        ForwardDeriver('%(interface)s_sc_size_bits', 'size_bits_attribute'),
        BackwardDeriver(r'^([^_].*)_sc_size_bits$', 'size_bits_attribute', 'interface'),
    ],
}

class Perspective(object):
    '''A partial state from which to mangle symbols. That may make no sense,
    but consider this as a collection of *some* of the symbols we need from
    which *all* the symbols we need can be derived. You need to pass some
    initial symbols in to the constructor. These may not be sufficient to
    derive all other known symbols, but they must be sufficient to derive any
    you need. The known symbols can be updated at any point via __setitem__. A
    more appropriate name for this class would be 'context', but I didn't want
    to cause confusion by introducing yet another 'context' into this code
    base.'''
    def __init__(self, phase=FILTERS, **kwargs):
        self.kwargs = kwargs
        self.derivations = DERIVATIONS[phase]
        if __debug__:
            # When optimisations are not enabled, infer everything possible
            # upfront (not lazily). This can catch some internal
            # inconsistencies though we will probably end up inferring things
            # we don't need.
            self._infer()

    def _infer(self, limit=None):
        '''Infer some or all possible unknown symbols. If the limit argument is
        given, inference stops when we know that symbol.'''
        prev_keys = set(self.kwargs.keys())
        while limit is None or limit not in prev_keys:
            for d in self.derivations:
                if d.inputs() <= set(self.kwargs.keys()):
                    # We have enough information to use this derivation.
                    v = d.derive(self.kwargs)
                    if v is None:
                        # We could not derive this value.
                        continue
                    k = d.output()
                    if k in self.kwargs:
                        # We already knew this symbol. It had better have been
                        # the same as what we just derived for consistency.
                        assert self.kwargs[k] == v, \
                            'perspective is internally inconsistent: %s' % self.kwargs
                    else:
                        self.kwargs[k] = v
            next_keys = set(self.kwargs.keys())
            if prev_keys == next_keys:
                # We didn't learn anything new this time around.
                break
            prev_keys = next_keys

    def __setitem__(self, key, value):
        assert key not in self.kwargs or self.kwargs[key] == value
        # The following assertion is conservative. In the future, it may make
        # sense to set some 'core' strings that we cannot infer.
        assert key in (x.output() for x in self.derivations), \
            'setting \'%s\' that is not inferrable' % key
        self.kwargs[key] = value
        if __debug__:
            self._infer()

    def __getitem__(self, key):
        # As for the assertion in __setitem__, this is conservative.
        assert key in (x.output() for x in self.derivations), \
            'getting \'%s\' that is not inferrable' % key
        if key not in self.kwargs:
            self._infer(key)
        if key not in self.kwargs:
            raise Exception('not enough information to infer attribute, %s' % key)
        return self.kwargs[key]
