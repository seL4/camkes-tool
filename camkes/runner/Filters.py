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
from .NameMangling import Perspective


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
    tcb_default_properties,
    tcb_properties,
    tcb_domains,
    remove_tcb_caps,
    sc_default_properties,
    sc_properties,
]
