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

"""Filters to be applied to generated CapDL."""
from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, six, subprocess
from capdl import Cap, CNode, TCB, SC, lookup_architecture
from camkes.internal.memoization import memoize
from .NameMangling import Perspective

PAGE_SIZE = 4096 # bytes

# PERF/HACK: This function is memoized and optionally calls out to objdump
# because it becomes a performance bottleneck in large systems. Note that the
# second branch here is much more reliable and you should use it when possible.
objdump_output = {}
@memoize()
def get_symbol(elf, symbol):
    objdump = None
    if os.environ.get('CONFIG_CAMKES_USE_OBJDUMP_ON', '') == 'y':
        objdump = '%sobjdump' % os.environ.get('TOOLPREFIX', '')
    elif os.environ.get('CONFIG_CAMKES_USE_OBJDUMP_AUTO', '') == 'y':
        with open(os.devnull, 'wt') as f:
            try:
                objdump = subprocess.check_output(['which', '%sobjdump' %
                    os.environ.get('TOOLPREFIX', '')], stderr=f,
                    universal_newlines=True).strip()
            except subprocess.CalledProcessError:
                objdump = None
    if objdump is not None:
        global objdump_output
        stdout = objdump_output.get(elf[0])
        if stdout is None:
            # We haven't run objdump on this output yet. Need to do it now.
            # Construct the bash invocation we want
            argument = "%s --syms %s | grep -E '^[0-9a-fA-F]{8}' | sed -r 's/^([0-9a-fA-F]{8,})[ \\t].*[ \\t]([0-9a-fA-F]{8,})[ \\t]+(.*)/\\3 \\1 \\2/'" % (objdump, elf[0])
            stdout = subprocess.check_output(['sh', '-c', argument],
                universal_newlines=True)
            # Cache the result for future symbol lookups.
            objdump_output[elf[0]] = stdout
        sym_index = stdout.find('\n%s ' % symbol)
        if sym_index == -1:
            return None, None
        end_index = stdout[sym_index+1:].find('\n')
        vaddr_start_index = sym_index + len(symbol) + 2
        if end_index == -1:
            substring = stdout[vaddr_start_index:]
        else:
            substring = stdout[vaddr_start_index:sym_index + end_index + 1]
        [vaddr, size] = substring.split()
        return int(vaddr, 16), int(size, 16)
    else:
        return elf[1].get_symbol_vaddr(symbol), elf[1].get_symbol_size(symbol)

def get_symbol_vaddr(elf, symbol):
    return get_symbol(elf, symbol)[0]
def get_symbol_size(elf, symbol):
    return get_symbol(elf, symbol)[1]

def set_tcb_info(cspaces, obj_space, elfs, options, **_):
    """Set relevant extra info for TCB objects."""
    arch = lookup_architecture(options.architecture)

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items()
                if v is not None and isinstance(v.referent, TCB)]:

            perspective = Perspective(group=group, tcb=tcb.name)

            elf_name = perspective['elf_name']

            elf = elfs.get(elf_name)

            if elf is None:
                # We were not passed an ELF file for this CSpace. This will be
                # true in the first pass of the runner where no ELFs are passed.
                continue

            tcb.elf = elf_name
            tcb.ip = get_symbol_vaddr(elf, perspective['entry_symbol'])
            assert tcb.ip != 0, 'entry point \'%s\' of %s appears to be 0x0' \
                % (perspective['entry_symbol'], tcb.name)

            if perspective['pool']:
                # This TCB is part of the (cap allocator's) TCB pool.
                continue

            stack_symbol = perspective['stack_symbol']
            ipc_buffer_symbol = perspective['ipc_buffer_symbol']

            # The stack should be at least three pages and the IPC buffer
            # region should be exactly three pages. Note that these regions
            # both include a guard page either side of the used area. It is
            # assumed that the stack grows downwards.
            stack_size = get_symbol_size(elf, stack_symbol)
            assert stack_size is not None, 'Stack for %(name)s, ' \
                '\'%(symbol)s\', not found' % {
                    'name':tcb.name,
                    'symbol':stack_symbol,
                }
            assert stack_size >= PAGE_SIZE * 3, 'Stack for %(name)s, ' \
                '\'%(symbol)s\', is only %(size)d bytes and does not have ' \
                'room for guard pages' % {
                    'name':tcb.name,
                    'symbol':stack_symbol,
                    'size':stack_size,
                }
            assert get_symbol_size(elf, ipc_buffer_symbol) == PAGE_SIZE * 3

            # Move the stack pointer to the top of the stack. Extra page is
            # to account for the (upper) guard page.
            assert stack_size % PAGE_SIZE == 0
            tcb.sp = get_symbol_vaddr(elf, stack_symbol) + stack_size - PAGE_SIZE
            tcb.addr = get_symbol_vaddr(elf, ipc_buffer_symbol) + \
                2 * PAGE_SIZE - arch.ipc_buffer_size()

            # Each TCB needs to be passed its 'thread_id' that is the value
            # it branches on in main(). This corresponds to the slot index
            # to a cap to it in the component's CNode.
            tcb.init.append(index)

            if options.realtime:
                sc_name = perspective['sc']
                if sc_name in obj_space:
                    # For non-passive threads, associate the sc with the tcb
                    sc = obj_space[sc_name]
                    tcb['sc_slot'] = Cap(sc)

def set_tcb_caps(ast, obj_space, cspaces, elfs, options, **_):
    arch = lookup_architecture(options.architecture)
    assembly = ast.assembly

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items()
                if v is not None and isinstance(v.referent, TCB)]:

            perspective = Perspective(tcb=tcb.name, group=group)

            # Finalise the CNode so that we know what its absolute size will
            # be. Note that we are assuming no further caps will be added to
            # the CNode after this point.
            cnode.finalise_size()

            # Allow the user to override CNode sizes with the 'cnode_size_bits'
            # attribute.
            cnode_size = assembly.configuration[group].get('cnode_size_bits')
            if cnode_size is not None:
                try:
                    if isinstance(cnode_size, six.string_types):
                        size = int(cnode_size, 0)
                    else:
                        size = cnode_size
                except ValueError:
                    raise Exception('illegal value for CNode size for %s' %
                        group)
                if size < cnode.size_bits:
                    raise Exception('%d-bit CNode specified for %s, but this '
                        'CSpace needs to be at least %d bits' %
                        (size, group, cnode.size_bits))
                cnode.size_bits = size

            cspace = Cap(cnode)
            cspace.set_guard_size(arch.word_size_bits() - cnode.size_bits)
            tcb['cspace'] = cspace

            pd = None
            pd_name = perspective['pd']
            pds = [x for x in obj_space.spec.objs if x.name == pd_name]
            if len(pds) > 1:
                raise Exception('Multiple PDs found for %s' % group)
            elif len(pds) == 1:
                pd, = pds
                tcb['vspace'] = Cap(pd)
            # If no PD was found we were probably just not passed any ELF files
            # in this pass.

            if perspective['pool']:
                # This TCB is part of the (cap allocator's) TCB pool.
                continue

            # Optional fault endpoints are configured in the per-component
            # template.

def guard_cnode_caps(cspaces, options, **_):
    """If the templates have allocated any caps to CNodes, they will not have
    the correct guards. This is due to the CNodes' sizes being automatically
    calculated (during set_tcb_caps above). Correct them here."""

    arch = lookup_architecture(options.architecture)
    for space in cspaces.values():
        [cap.set_guard_size(arch.word_size_bits() - cap.referent.size_bits)
            for cap in space.cnode.slots.values()
            if cap is not None and isinstance(cap.referent, CNode)]

def tcb_default_properties(obj_space, options, **_):
    """Set up default thread priorities. Note this filter needs to operate
    *before* tcb_priorities."""

    for t in [x for x in obj_space if isinstance(x, TCB)]:
        t.prio = options.default_priority
        t.max_prio = options.default_max_priority
        t.affinity = options.default_affinity

def sc_default_properties(obj_space, options, **_):
    """Set up default scheduling context properties. Note this filter needs to operate
    *before* sc_properties."""

    for s in (x for x in obj_space if isinstance(x, SC)):
        s.period = options.default_period
        s.budget = options.default_budget
        s.data = options.default_data
        s.size_bits = options.default_size_bits

def maybe_set_property_from_configuration(assembly, perspective, obj, field_name, attribute_name, general_attribute):
    """Sets a field "field_name" of an object "obj" to the value of a configuration
    setting of the form:
    instance.attribute = value;
    where "instance" and "attribute" are obtained from the perspective argument
    which is queried for the current instance, and the value corresponding to
    attribute_name respectively.
    If such a setting exists, the field is set.
    Otherwise, check if a corresponding general property was set for the instance.
    This is a setting that applies the property to all threads related to the instance
    including all interface threads."""

    name = perspective['instance']
    attribute = perspective[attribute_name]
    value = assembly.configuration[name].get(attribute)
    if value is None:
        general_value = assembly.configuration[name].get(general_attribute)
        if general_value is not None:
            setattr(obj, field_name, general_value)
    else:
        setattr(obj, field_name, value)

def tcb_properties(ast, cspaces, options, **_):
    """ Override a TCB's default property if the user has specified this in an
    attribute."""

    assembly = ast.assembly

    if len(assembly.configuration.settings) == 0:
        # We have nothing to do if no properties were set.
        return

    # The pattern of the names of fault handler threads.
    def is_fault_handler(tcb_name):
        p = Perspective(tcb=tcb_name)
        return not p['control'] and p['interface'] == '0_fault_handler'

    for group, space in cspaces.items():
        cnode = space.cnode
        for tcb in [v.referent for v in cnode.slots.values()
                if v is not None and isinstance(v.referent, TCB)]:

            assert options.debug_fault_handlers or not \
                is_fault_handler(tcb.name), 'fault handler threads present ' \
                'without fault handlers enabled'

            # If the current thread is a fault handler, we don't want to let
            # the user alter its priority. Instead we set it to the highest
            # priority to ensure faults are always displayed. Note that this
            # will not prevent other threads running because the fault handlers
            # are designed to be blocked when not handling a fault.
            if is_fault_handler(tcb.name):
                tcb.prio = 255
                continue

            perspective = Perspective(group=group, tcb=tcb.name)

            maybe_set_property_from_configuration(assembly, perspective, tcb, 'prio', 'priority_attribute', 'priority')
            maybe_set_property_from_configuration(assembly, perspective, tcb, 'max_prio', 'max_priority_attribute', 'max_priority')
            maybe_set_property_from_configuration(assembly, perspective, tcb, 'affinity', 'affinity_attribute', 'affinity')

def sc_properties(ast, cspaces, obj_space, **_):
    """ Override an SC's default properties if the user has specified this in an
    attribute."""

    assembly = ast.assembly

    if len(assembly.configuration.settings) == 0:
        # We have nothing to do if no properties were set.
        return

    for group, space in cspaces.items():
        cnode = space.cnode
        for sc in (cap.referent for cap in cnode.slots.values()
                if cap is not None and isinstance(cap.referent, SC)):

            if sc.name.endswith("passive_init_sc"):
                # SC is used for passive init.
                # Set its properties based on its instance's timing settings.
                perspective = Perspective(group=group, passive_init_sc=sc.name)
            else:
                # SC belongs to a thread (interface thread or instance main thread).
                # Set properties according to the instance or interface settings.
                perspective = Perspective(group=group, sc=sc.name)

            maybe_set_property_from_configuration(assembly, perspective, sc, 'period', 'period_attribute', 'period')
            maybe_set_property_from_configuration(assembly, perspective, sc, 'budget', 'budget_attribute', 'budget')
            maybe_set_property_from_configuration(assembly, perspective, sc, 'data', 'data_attribute', 'data')
            maybe_set_property_from_configuration(assembly, perspective, sc, 'size_bits', 'size_bits_attribute', 'size_bits')

def tcb_domains(ast, cspaces, **_):
    """Set the domain of a TCB if the user has specified this in an
    attribute."""

    assembly = ast.assembly

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no domains were set.
        return

    for group, space in cspaces.items():
        cnode = space.cnode
        for tcb in [x.referent for x in cnode.slots.values() if
                (x is not None and isinstance(x.referent, TCB))]:

            perspective = Perspective(group=group, tcb=tcb.name)

            # Find the domain if it was set.
            dom_attribute = perspective['domain_attribute']
            name = perspective['instance']
            dom = assembly.configuration[name].get(dom_attribute)

            if dom is not None:
                tcb.domain = dom

def remove_tcb_caps(cspaces, options, **_):
    """Remove all TCB caps in the system if requested by the user."""
    if not options.fprovide_tcb_caps:
        for space in cspaces.values():
            for slot in [k for (k, v) in space.cnode.slots.items()
                    if v is not None and isinstance(v.referent, TCB)]:
                del space.cnode[slot]

CAPDL_FILTERS = [
    set_tcb_info,
    set_tcb_caps,
    guard_cnode_caps,
    tcb_default_properties,
    tcb_properties,
    tcb_domains,
    remove_tcb_caps,
    sc_default_properties,
    sc_properties,
]
