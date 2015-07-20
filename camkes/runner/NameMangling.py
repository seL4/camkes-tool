#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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

from camkes.internal.dictutils import get_fields
import re

class Deriver(object):
    '''Logic for constructing one symbol from one or more other symbols. This
    class itself is never intended to be directly instantiated and is probably
    best understood by looking at its inherited children.'''
    def inputs(self):
        raise NotImplementedError
    def output(self):
        raise NotImplementedError
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

# Phases.
RUNNER, TEMPLATES, FILTERS = range(3)

# Instantiate the derivers to describe how name mangling happens in CAmkES. If
# you want to modify the name mangling scheme, this is the place to do it.
DERIVATIONS = {
    RUNNER:[
        ForwardDeriver('pd_%(group)s_group_bin', 'pd'),
        ForwardDeriver('pd_%(elf_name)s', 'pd'),
        BackwardDeriver(r'^pd_(.+)$', 'pd', 'elf_name'),
        BackwardDeriver(r'^pd_(.+)_group_bin$', 'pd', 'group'),
        ForwardDeriver('cnode_%(group)s', 'cnode'),
        BackwardDeriver(r'^cnode_(.+)$', 'cnode', 'group'),
    ], TEMPLATES:[
        ForwardDeriver('dma_frame_%(dma_frame_index)s', 'dma_frame_symbol'),
        DMAFrameIndexDeriver(r'^dma_frame_([0-9]+)$', 'dma_frame_symbol'),
        ForwardDeriver('_camkes_ipc_buffer_%(instance)s_%(interface)s', 'ipc_buffer_symbol'),
        FromControlDeriver('_camkes_ipc_buffer_%(instance)s_0_control', 'ipc_buffer_symbol'),
        ControlDeriver(r'^_camkes_ipc_buffer_.+_0_control$', 'ipc_buffer_symbol'),
        ForwardDeriver('_camkes_stack_%(instance)s_%(interface)s', 'stack_symbol'),
        FromControlDeriver('_camkes_stack_%(instance)s_0_control', 'stack_symbol'),
        ControlDeriver(r'^_camkes_stack_.+_0_control$', 'stack_symbol'),
        ForwardDeriver('%(dataport)s_data', 'dataport_symbol'),
        BackwardDeriver(r'^([^ ]+)_data$', 'dataport_symbol', 'dataport'),
        ForwardDeriver('%(to_interface)s_attributes', 'hardware_attribute'),
        BackwardDeriver(r'^(.+)_attributes', 'hardware_attribute', 'to_interface'),
        ForwardDeriver('%(group)s_group_bin', 'elf_name'),
        BackwardDeriver(r'^(.+)_group_bin', 'elf_name', 'group'),
        ForwardDeriver('%(instance)s_main', 'entry_symbol'),
        BackwardDeriver(r'^(.+)_main$', 'entry_symbol', 'instance'),
        ForwardDeriver('%(instance)s_tls_setup', 'tls_symbol'),
        BackwardDeriver(r'^(.+)_tls_setup$', 'tls_symbol', 'instance'),
        ForwardDeriver('camkes_dma_pool', 'dma_pool_symbol'),
    ], FILTERS:[
        ForwardDeriver('%(instance)s_tcb_%(interface)s', 'tcb'),
        FromControlDeriver('%(instance)s_tcb_0_control', 'tcb'),
        BackwardDeriver(r'^(.+)_tcb_.+$', 'tcb', 'instance'),
        BackwardDeriver(r'^.+_tcb_([a-zA-Z_]\w*)$', 'tcb', 'interface'),
        ControlDeriver(r'^.+_tcb_0_control$', 'tcb'),
        ForwardDeriver('_camkes_ipc_buffer_%(instance)s_%(interface)s', 'ipc_buffer_symbol'),
        FromControlDeriver('_camkes_ipc_buffer_%(instance)s_0_control', 'ipc_buffer_symbol'),
        ControlDeriver(r'^_camkes_ipc_buffer_.+_0_control$', 'ipc_buffer_symbol'),
        ForwardDeriver('_camkes_stack_%(instance)s_%(interface)s', 'stack_symbol'),
        FromControlDeriver('_camkes_stack_%(instance)s_0_control', 'stack_symbol'),
        ControlDeriver(r'^_camkes_stack_.+_0_control$', 'stack_symbol'),
        ForwardDeriver('camkes %(instance)s_main', 'entry_symbol'),
        BackwardDeriver(r'^camkes (.+)_main$', 'entry_symbol', 'instance'),
        ForwardDeriver('camkes %(instance)s_tls_setup', 'tls_symbol'),
        BackwardDeriver(r'^camkes (.+)_tls_setup$', 'tls_symbol', 'instance'),
        ForwardDeriver('%(group)s_group_bin', 'elf_name'),
        BackwardDeriver(r'^(.+)_group_bin', 'elf_name', 'group'),
        PoolDeriver(r'.+_tcb_pool_[0-9]+$', 'tcb'),
        PoolIndexDeriver(r'.+_tcb_pool_([0-9]+)$', 'tcb'),
        ForwardDeriver('pd_%(group)s_group_bin', 'pd'),
        ForwardDeriver('pd_%(elf_name)s', 'pd'),
        BackwardDeriver(r'^pd_(.+)$', 'pd', 'elf_name'),
        BackwardDeriver(r'^pd_(.+)_group_bin$', 'pd', 'group'),
        ForwardDeriver('camkes %(instance)s %(dataport)s data', 'dataport_symbol'),
        BackwardDeriver(r'^camkes ([^ ]+) [^ ]+ data$', 'dataport_symbol', 'instance'),
        BackwardDeriver(r'^camkes [^ ]+ ([^ ]+) data$', 'dataport_symbol', 'dataport'),
        ForwardDeriver('%(to_interface)s_attributes', 'hardware_attribute'),
        BackwardDeriver(r'^(.+)_attributes', 'hardware_attribute', 'to_interface'),
        ForwardDeriver('camkes %(instance)s_dma_pool', 'dma_pool_symbol'),
        BackwardDeriver(r'^camkes (.+)_dma_pool$', 'dma_pool_symbol', 'instance'),
        ForwardDeriver('%(instance)s_dma_frame_%(dma_frame_index)s', 'dma_frame_symbol'),
        BackwardDeriver(r'^(.+)_dma_frame_[0-9]+$', 'dma_frame_symbol', 'instance'),
        DMAFrameIndexDeriver(r'^.+_dma_frame_([0-9]+)$', 'dma_frame_symbol'),
        ControlDeriver(r'^_priority$', 'priority_attribute'),
        FromControlDeriver('_priority', 'priority_attribute'),
        ForwardDeriver('%(interface)s_priority', 'priority_attribute'),
        BackwardDeriver(r'^([a-zA-Z_]\w*)_priority$', 'priority_attribute', 'interface'),
        ControlDeriver(r'^_domain$', 'domain_attribute'),
        FromControlDeriver('_domain', 'domain_attribute'),
        ForwardDeriver('%(interface)s_domain', 'domain_attribute'),
        BackwardDeriver(r'^([a-zA-Z_]\w*)_domain$', 'domain_attribute', 'interface'),
        ForwardDeriver('cnode_%(group)s', 'cnode'),
        BackwardDeriver(r'^cnode_(.+)$', 'cnode', 'group'),
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
        assert key in map(lambda x: x.output(), self.derivations), \
            'setting \'%s\' that is not inferrable' % key
        self.kwargs[key] = value
        if __debug__:
            self._infer()

    def __getitem__(self, key):
        # As for the assertion in __setitem__, this is conservative.
        assert key in map(lambda x: x.output(), self.derivations), \
            'getting \'%s\' that is not inferrable' % key
        if key not in self.kwargs:
            self._infer(key)
        if key not in self.kwargs:
            raise Exception('not enough information to infer attribute, %s' % key)
        return self.kwargs[key]
