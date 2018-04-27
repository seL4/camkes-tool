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

# Macros for use inside the templates.

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import Composition, Instance, Parameter, Struct
from camkes.templates import sizeof_probe
from capdl import ASIDPool, CNode, Endpoint, Frame, IODevice, IOPageTable, \
    Notification, page_sizes, PageDirectory, PageTable, TCB, Untyped, \
    calculate_cnode_size
import collections, math, os, platform, re, six

from camkes.templates.arch_helpers import min_untyped_size, max_untyped_size

def thread_stack(sym, size='CONFIG_CAMKES_DEFAULT_STACK_SIZE'):
    return 'char %s[ROUND_UP_UNSAFE(%s, ' \
                'PAGE_SIZE_4K) + PAGE_SIZE_4K * 2]\n' \
           '    VISIBLE\n' \
           '    __attribute__((section("guarded")))\n' \
           '    ALIGN(PAGE_SIZE_4K);\n' % (sym, size)

def ipc_buffer(sym):
    return 'char %s[PAGE_SIZE_4K * 3]\n' \
           '    VISIBLE\n' \
           '    __attribute__((section("guarded")))\n' \
           '    ALIGN(PAGE_SIZE_4K);\n' % sym

def save_ipc_buffer_address(sym):
    return '#ifdef CONFIG_ARCH_X86\n' \
           '    /* We need to save the address of the IPC buffer (for\n' \
           '     * marshalling/unmarshalling) per-thread. Essentially what we\'re after\n' \
           '     * is TLS. Use the IPC buffer\'s user data word for that. Note that we\n' \
           '     * add a page to skip over the guard page in front of the IPC buffer.\n' \
           '     */\n' \
           '    seL4_SetUserData((seL4_Word)%s + 2 * PAGE_SIZE_4K - sizeof(seL4_IPCBuffer));\n' \
           '#endif\n' % sym

def show_type(t):
    assert isinstance(t, (six.string_types, Struct))
    if isinstance(t, six.string_types):
        if t == 'string':
            return 'char *'
        elif t == 'character':
            return 'char'
        elif t == 'boolean':
            return 'bool'
        else:
            return t
    else:
        return "struct " + t.name

def print_type_definitions(attributes, values):
    def print_struct_definition(struct, sub_value):
        return_string = "struct %s {\n" % struct.name
        for i in struct.attributes:
            return_string += "%s %s%s;\n" % (show_type(i.type), i.name, "[%d]" % len(sub_value.get(i.name)) if i.array else "")
        return return_string + "};\n"

    def recurse_structs(attribute, values):
        struct = attribute.type
        structs = []
        for sub_attribute in struct.attributes:
            if isinstance(sub_attribute.type, Struct):
                structs.extend(recurse_structs(sub_attribute, values.get(sub_attribute.name)))
        structs.append((struct, values))
        return structs

    return_string = ""
    structs = []
    for attribute in attributes:
        if isinstance(attribute.type, Struct):
            structs.extend(recurse_structs(attribute, values.get(attribute.name)))

    already_drawn = dict()
    for (struct, sub_value) in structs:
        if struct.name not in already_drawn:
            return_string += str(print_struct_definition(struct, sub_value))
            already_drawn[struct.name] = 1

    return return_string

def show_attribute_value(t, value):
    """ Prints out an attributes value.
        An attriubte can be an array (although this is provided to the template as a tuple type)
        An attribute can also be a camkes structure which is a dictionary of attributes (keys) with corresponding values
    """
    return_string = ""
    is_array = False
    if isinstance(value, (tuple, list)):
        is_array = True
        values = value
        return_string += "{\n"
    else:
        values = (value,)

    # runs for every element in the array, if a non array attribute then this just runs once.
    for i, value in enumerate(values):
        if isinstance(value, six.string_types): # For string literals
            return_string +=  "\"%s\"" % value
        elif isinstance(t.type, Struct): # For struct attributes (This recursively calls this function)
            return_string += "{\n"
            for attribute in t.type.attributes:
                return_string += "." + str(attribute.name) #+ ("[]" if attribute.array else "")
                return_string += " = " + str(show_attribute_value(attribute, value[attribute.name])) + ",\n"
            return_string += "}"
        else: # For all other literal types
            return_string += "%s" % str(value)

        # Add comma if element is part of an array
        if i < (len(values)-1):
            return_string += ",\n"
    if is_array:
        return_string += "}"
    return return_string

def show_includes(xs, prefix=''):
    s = ''
    for header in xs:
        if header.relative:
            s += '#include "%(prefix)s%(source)s"\n' % {
                'prefix':prefix,
                'source':header.source,
            }
        else:
            s += '#include <%s>\n' % header.source
    return s

def format_list_of_strings(string, list, seperator):
    return seperator.join(string % elem for elem in list)

def threads(composition, instance):
    '''
    Compute the threads for a given instance.

    This function could be written more efficiently as a generator, but it is
    assumed that most callers (in the template context) will need to repeatedly
    iterate over it, so will get no benefit from this.
    '''
    assert isinstance(composition, Composition)
    assert isinstance(instance, Instance)
    class Thread(object):
        def __init__(self, interface, intra_index):
            self.interface = interface
            self.intra_index = intra_index
    ts = [Thread(None, 0)]
    for connection in composition.connections:
        for end in connection.from_ends:
            if end.instance == instance:
                ts.extend(Thread(end.interface, x) for x in
                    six.moves.range(connection.type.from_threads))
        for end in connection.to_ends:
            if end.instance == instance:
                ts.extend(Thread(end.interface, x) for x in
                    six.moves.range(connection.type.to_threads))
    return ts

def dataport_size(type):
    assert isinstance(type, six.string_types)
    m = re.match(r'Buf\((\d+)\)$', type)
    if m is not None:
        return m.group(1)
    return 'sizeof(%s)' % show_type(type)

def dataport_type(type):
    assert isinstance(type, six.string_types)
    if re.match(r'Buf\((\d+)\)$', type) is not None:
        return 'void'
    return show_type(type)

# The following macros are for when you require generation-time constant
# folding. These are not robust and for cases when a generation-time constant
# is not required, you should simply emit the C equivalent and let the C
# compiler handle it.

PAGE_SIZE = 4096

def ROUND_UP(x, y):
    return int(int(math.ceil(int(x) / float(y))) * y)

_sizes = {
    # The sizes of a few things we know statically.
    'Buf':4096,
    'int8_t':1,
    'uint8_t':1,
    'int16_t':2,
    'uint16_t':2,
    'int32_t':4,
    'uint32_t':4,
    'int64_t':8,
    'uint64_t':8,
}
def sizeof(arch, t):
    assert isinstance(t, (Parameter,) + six.string_types)

    if isinstance(t, Parameter):
        return sizeof(arch, t.type)

    size = _sizes.get(t)
    if size is None:
        # We don't know the size of this type, so we'll ask the C compiler.
        toolprefix = os.environ.get('TOOLPREFIX', '')
        compiler = '%sgcc' % toolprefix

        extra_flags = []
        # Account for the fact that we may be cross-compiling using our native
        # compiler.
        if arch == 'ia32' and platform.machine() == 'x86_64':
            extra_flags.append('-m32')
        elif arch == 'x86_64' and platform.machine() == 'i386':
            extra_flags.append('-m64')

        # Determine the size by invoking the c compiler
        size = sizeof_probe.probe_sizeof(t, compiler, extra_flags)

        # Cache the result for next time.
        _sizes[t] = size

    assert size is not None
    return size

def to_isabelle_set(xs):
    assert isinstance(xs, collections.Iterable)
    if all(isinstance(x, six.string_types) for x in xs):
        return '{%s}' % ', '.join('\'\'%s\'\'' % x for x in xs)
    raise NotImplementedError

def capdl_sorter(arch, a, b):
    '''
    This function replicates `sorter` from the CapDL translator. The purpose is
    to enable us to sort objects in templates in the same way that the
    translator does.
    '''

    def size_of(obj):
        '''
        This function logic is clagged from the CapDL translator's `sizeOf`.
        '''
        if isinstance(obj, Frame):
            return obj.size
        elif isinstance(obj, Untyped):
            return 2 ** obj.size_bits
        elif isinstance(obj, CNode):
            if obj.size_bits == 'auto':
                return calculate_cnode_size(obj)
            return 16 * 2 ** obj.size_bits
        elif isinstance(obj, Endpoint):
            return 16
        elif isinstance(obj, Notification):
            return 16
        elif isinstance(obj, ASIDPool):
            return 4 * 2 ** 10
        elif isinstance(obj, IOPageTable):
            return 4 * 2 ** 10
        elif isinstance(obj, IODevice):
            return 1
        elif isinstance(obj, TCB):
            if arch in ('aarch32', 'arm_hyp'):
                return 512
            elif arch == 'ia32':
                return 2 ** 10
            raise NotImplementedError('size_of TCB for arch: %s' % arch)
        elif isinstance(obj, PageDirectory):
            if arch in ('aarch32', 'arm_hyp'):
                return 16 * 2 ** 10
            elif arch == 'ia32':
                return 4 * 2 ** 10
            raise NotImplementedError('size_of PageDirectory for arch: %s' % arch)
        elif isinstance(obj, PageTable):
            if arch == 'aarch32':
                return 2 ** 10
            elif arch == 'arm_hyp':
                return 2 * 2 ** 10
            elif arch == 'ia32':
                return 4 * 2 ** 10
            raise NotImplementedError('size_of PageTable for arch: %s' % arch)
        raise NotImplementedError('size_of for type: %s' % type(obj))

    def get_paddr(obj):
        '''Also clagged from CapDL translator. If obj has a paddr, place it after
           other objs and sort by paddr.'''
        if (isinstance(obj, Frame) or isinstance(obj, Untyped)) and obj.paddr is not None:
            return obj.paddr
        else:
            return 1

    a_key, b_key = (get_paddr(a), -size_of(a), a.name), (get_paddr(b), -size_of(b), b.name)
    return (a_key > b_key) - (a_key < b_key)
