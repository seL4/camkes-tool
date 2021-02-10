#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''
The jinja2 template code runs in a very restricted environment during
rendering. For example, you can't call functions like `map`. To expose certain
functions to the template code we need to explicitly pass these in during
rendering. This module encapsulates extra context elements we want to make
available to the template code.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from functools import partial
import capdl
import code
import collections
import copy
import inspect
import itertools
import functools
import numbers
import \
    orderedset, os, pdb, re, six, sys, textwrap, math
from capdl.Object import ObjectType, ObjectRights, ARMIRQMode
from capdl.Allocator import Cap
from capdl import page_sizes

# Depending on what kernel branch we are on, we may or may not have ASIDs.
# There are separate python-capdl branches for this, but this import allows us
# to easily interoperate with both.
try:
    from capdl.Allocator import seL4_ASID_Pool
except ImportError:
    seL4_ASID_Pool = None

import camkes.ast as AST
from camkes.internal.Counter import Counter
from camkes.templates import macros, TemplateError


def new_context(entity, assembly, render_state, state_key, outfile_name,
                **kwargs):
    '''Create a new default context for rendering.'''

    obj_space = render_state.obj_space if render_state else None
    cap_space = render_state.cspaces[state_key] if state_key and render_state else None
    addr_space = render_state.addr_spaces[state_key] if state_key and render_state else None

    return dict(list(__builtins__.items()) + list(ObjectType.__members__.items()) + list(ObjectRights.__members__.items()) + list(ARMIRQMode.__members__.items()) + list({
        # Kernel object allocator
        'alloc_obj': (
            lambda name, type, label=entity.label(), **kwargs:
                alloc_obj((entity.label(), obj_space), obj_space,
                          '%s_%s' % (entity.label(), name), type, label,
                          **kwargs))
        if obj_space else None,

        # Cap allocator
        'alloc_cap': None if cap_space is None else \
                (lambda name, obj, **kwargs: alloc_cap((entity.label(),
                                                        cap_space), cap_space, name, obj, **kwargs)),

                'Cap': Cap,

                # The CNode root of your CSpace. Should only be necessary in cases
                # where you need to allocate a cap to it.
                'my_cnode': None if cap_space is None else cap_space.cnode,

                # Batched object and cap allocation for when you don't need a reference
                # to the object. Probably best not to look directly at this one. When
                # you see `set y = alloc('foo', bar, moo)` in template code, think:
                #  set x = alloc_obj('foo_obj', bar)
                #  set y = alloc_cap('foo_cap', x, moo)
                'alloc': None if cap_space is None else \
                (lambda name, type, label=entity.label(), **kwargs:
                 alloc_cap((entity.label(), cap_space), cap_space, name,
                           alloc_obj((entity.label(), obj_space), obj_space, '%s_%s' %
                                     (entity.label(), name), type, label, **kwargs),
                           **kwargs)),

                # Functionality for templates to inform us that they've emitted a C
                # variable that's intended to map to a shared variable. It is
                # (deliberately) left to the template authors to ensure global names
                # (gnames) only collide when intended; i.e. when they should map to the
                # same shared variable. The local name (lname) will later be used by us
                # to locate the relevant ELF frame(s) to remap. Note that we assume
                # address spaces and CSpaces are 1-to-1.
                'register_shared_variable': None if cap_space is None else \
                (lambda global_name, symbol, size, frame_size=None, paddr=None,
                 perm='RWX', cached=True, label=entity.parent.label(), with_mapping_caps=None:
                 register_shared_variable(
                     addr_space, obj_space, global_name, symbol, size, cap_space,
                     frame_size, paddr, perm, cached, label, with_mapping_caps)),

                'get_shared_variable_backing_frames': None if cap_space is None else \
                (lambda global_name, size, frame_size=None, label=entity.parent.label():
                 get_shared_variable_backing_frames(
                    obj_space, global_name, size, frame_size, label)),

                # Get the object-label mapping for our verification models.
                'object_label_mapping': (lambda: object_label_mapping(obj_space)),

                # Function for templates to inform us that they would like certain
                # 'fill' information to get placed into the provided symbol. Provided
                # symbol should be page size and aligned. The 'fill' parameter is
                # an arbitrary string that will be set as the 'fill' parameter on the
                # capDL frame object. The meaning of fill is completely dependent
                # on the underlying loader
                'register_fill_frame': (lambda symbol, fill, size=4096:
                                        register_fill_frame(addr_space, symbol, fill, size, obj_space, entity.label())),

                'register_stack_symbol': (lambda symbol, size:
                                          register_stack_symbol(addr_space, symbol, size, obj_space, entity.label())),

                'register_ipc_symbol': (lambda symbol, frame:
                                        register_ipc_symbol(addr_space, symbol, frame)),

                'register_dma_pool': (lambda symbol, page_size, caps:
                                      register_dma_pool(addr_space, symbol, page_size, caps, cap_space)),

                # A `self`-like reference to the current AST object. It would be nice
                # to actually call this `self` to lead to more pythonic templates, but
                # `self` inside template blocks refers to the jinja2 parser.
                'me': entity,

                # The AST assembly's configuration.
                'configuration': assembly.configuration,

                # The AST assembly's composition
                'composition': assembly.composition,

                # Cross-template variable passing helpers. These are quite low-level.
                # Avoid calling them unless necessary.
                'stash': partial(stash, entity.label()),
                'pop': partial(pop, entity.label()),
                'guard': partial(guard, entity.label()),

                # If the previous group of functions are considered harmful, these are
                # to be considered completely off limits. These expose a mechanism for
                # passing data between unrelated templates (_stash and _pop) and a way
                # of running arbitrary Python statements and expressions. They come
                # with significant caveats. E.g. _stash and _pop will likely not behave
                # as expected with the template cache enabled.
                '_stash': partial(stash, ''),
                '_pop': partial(pop, ''),
                'exec': _exec,

                # Helpers for creating unique symbols within templates.
                'c_symbol': partial(symbol, '_camkes_%(tag)s_%(counter)d'),
                'isabelle_symbol': partial(symbol, '%(tag)s%(counter)d\'', 's'),

                # Expose some library functions
                'assert': _assert,
                'itertools': itertools,
                'functools': functools,
                'lambda': lambda s: eval('lambda %s' % s),
                'numbers': numbers,
                'os': os,
                'pdb': pdb,
                'raise': _raise,
                're': re,
                'six': six,
                'set': orderedset.OrderedSet,
                'textwrap': textwrap,
                'copy': copy,
                'zip': zip,
                'math': math,
                'enumerate': enumerate,

                # Allocation pools. In general, do not touch these in templates, but
                # interact with them through the alloc* functions. They are only in the
                # context to allow unanticipated template extensions.
                'obj_space': obj_space,
                'cap_space': cap_space,

                # Debugging functions
                'breakpoint': _breakpoint,
                'sys': sys,

                # Work around for Jinja's bizarre scoping rules.
                'Counter': Counter,

                # Return a list of distinct elements. Normally you would just do this
                # as list(set(xs)), but this turns out to be non-deterministic in the
                # template environment for some reason.
                'uniq': lambda xs: functools.reduce(lambda ys, z: ys if z in ys else (ys + [z]), xs, []),

                # Functional helpers.
                'flatMap': lambda f, xs: list(itertools.chain.from_iterable(map(f, xs))),
                'flatten': lambda xss: list(itertools.chain.from_iterable(xss)),

                # Macros for common operations.
                'macros': macros,

                # Macro shorthands for mangling Isabelle identifiers.
                'isabelle_identifier': macros.isabelle_ident,
                'isabelle_component':  macros.isabelle_ADL_ident('component'),
                'isabelle_instance':   macros.isabelle_ADL_ident('instance'),
                'isabelle_connector':  macros.isabelle_ADL_ident('connector'),
                'isabelle_connection': macros.isabelle_ADL_ident('connection'),
                'isabelle_procedure':  macros.isabelle_ADL_ident('procedure'),
                'isabelle_event':      macros.isabelle_ADL_ident('event'),
                'isabelle_dataport':
                    lambda name: macros.isabelle_ADL_ident('dataport')(
                    # hack to fix up names for sized buffer types e.g. 'Buf(4096)' -> 'Buf_4096'
            re.sub(r'\((.*)\)', r'_\1', name)),

        'isabelle_capdl_identifier': macros.isabelle_ident,

        # Add extra policy edges to help the cdl-refine verification.
        'add_policy_extra': lambda x, auth, y: render_state.policy_extra.add((x, auth, y)),
        'get_policy_extra': lambda: set(render_state.policy_extra),

        # This function abstracts away the differences between the RT kernel's
        # seL4_Recv and the master kernel's seL4_Recv. Namely, the RT kernel's
        # seL4_Recv takes an extra reply object cap.
        #
        # seL4_Recv is distinct from seL4_Wait, in that a seL4_Recv() call
        # expects to potentially get a reply cap from the sender.
        'generate_seL4_Recv': generate_seL4_Recv,

        # This function is similar to generate_seL4_Recv, in that it also
        # abstracts away the differences between the RT and master kernels.
        # This function specifically abstracts away the differences between
        # seL4_SignalRecv (on master) and seL4_NBSendRecv (on RT).
        'generate_seL4_SignalRecv': generate_seL4_SignalRecv,

        # This function is similar to generate_seL4_Recv as well, but it
        # abstracts away the differences between seL4_ReplyRecv between the
        # RT and master branches.
        'generate_seL4_ReplyRecv': generate_seL4_ReplyRecv,

        # Give template authors access to AST types just in case. Templates
        # should never be constructing objects of these types, but they may
        # need to do `isinstance` testing.
        'camkes': collections.namedtuple('camkes', ['ast'])(AST),

        # Expose CapDL module for `isinstance` testing.
        'capdl': capdl,

        # Give the template authors a mechanism for writing C-style include
        # guards. Use the following idiom to guard an include target:
        #  /*- if 'template.filename' not in included' -*/
        #  /*- do included.add('template.filename') -*/
        #  ... my template ...
        #  /*- endif -*/
        'included': set(),

        # Expose an exception class templates can use to throw errors related
        # to invalid input specification.
        'TemplateError': TemplateError,

        # Output filename (mainly needed by Isabelle templates)
        # Currently only supported for misc templates.
        'outfile_name': outfile_name,

        # FIXME: these are currently used in cdl-refine.thy,
        # but should be done in a cleaner way.
        'is_IRQ_object': lambda obj: isinstance(obj, capdl.IRQ),
        'is_ASIDPool_object': lambda obj: isinstance(obj, capdl.ASIDPool),
    }.items()) + list(kwargs.items()))


# For all three of these functions below, for the 'badge_var_name' variable,
# be sure that you pass in an ampersand character prefixed to the argument if
# your badge variable isn't a pointer.


def generate_seL4_Recv(options, ep_cap, badge_var_name, reply_cap):
    if options.realtime:
        return 'seL4_Recv(%s, %s, %s)' % (ep_cap, badge_var_name, reply_cap)
    else:
        return 'seL4_Recv(%s, %s)' % (ep_cap, badge_var_name)


def generate_seL4_SignalRecv(options, res_msginfo_var_name, dest_ntfn_cap, dest_msginfo_var_name, src_ep_cap, badge_var_name, reply_cap):
    if options.realtime:
        return '%s = seL4_NBSendRecv(%s, %s, %s, %s, %s)' % (res_msginfo_var_name, dest_ntfn_cap, dest_msginfo_var_name, src_ep_cap, badge_var_name, reply_cap)
    else:
        return 'seL4_Signal(%s); %s = seL4_Recv(%s, %s)' % (dest_ntfn_cap, res_msginfo_var_name, src_ep_cap, badge_var_name)


def generate_seL4_ReplyRecv(options, src_ep_cap, dest_msginfo_var_name, badge_var_name, reply_cap):
    if options.realtime:
        return 'seL4_ReplyRecv(%s, %s, %s, %s)' % (src_ep_cap, dest_msginfo_var_name, badge_var_name, reply_cap)
    else:
        return 'seL4_ReplyRecv(%s, %s, %s)' % (src_ep_cap, dest_msginfo_var_name, badge_var_name)


def _assert(condition, msg=None):
    '''Hack to reify assert as a callable'''
    if msg is not None:
        assert condition, msg
    else:
        assert condition
    return ''


def _exec(statement):
    '''Hack to reify exec as a callable'''
    # Jinja seems to invoke this through a variable level of indirection.
    # Search up our stack for the caller's context, identifiable by their 'me'
    # variable. This is a bit fragile, but since _exec should only be a tool of
    # last resort, I think it's acceptable.
    stack_frames = inspect.stack()
    caller = None
    for i, f in enumerate(stack_frames):
        if 'me' in f[0].f_locals:
            # Found it.
            caller = i
            break
    if caller is None:
        raise Exception('_exec: failed to find caller\'s context')
    six.exec_(statement, stack_frames[caller][0].f_globals,
              stack_frames[caller][0].f_locals)
    return ''


def _raise(exception):
    '''Hack to reify raise as a callable'''
    if isinstance(exception, Exception):
        raise exception
    else:
        assert hasattr(exception, '__call__')
        raise exception()
    return ''


def _breakpoint():
    '''Debugging function to be called from templates. This drops you into the
    Python interpreter with a brief attempt to align your locals() with the
    template's.'''
    kwargs = {
        'banner': 'Breakpoint triggered',
    }

    # Try and locate the stack frame containing the template context. This is a
    # bit error prone, but it's nice if we can find it because then we can fake
    # the template context to the interpreter prompt.
    for f in inspect.stack():
        if 'context' in f[0].f_locals:
            kwargs['local'] = f[0].f_globals.copy()
            kwargs['local'].update(f[0].f_locals['context'])
            break

    code.interact(**kwargs)

    # It's possible the template called this from inside a /*? ?*/ block, so
    # make sure we don't mess up the output:
    return ''


# Functionality for carrying variables between related templates. The idea is
# that one template performs stash('foo', 'bar') to save 'bar' and the other
# template performs pop('foo') to retrieve 'bar'. This pattern relies on the
# order of instantiation of templates. To avoid this, use the guard function
# below. See the templates for examples.
store = {}


def stash(client, key, value):
    if client not in store:
        store[client] = {}
    store[client][key] = value
    return ''


def pop(client, key):
    if client not in store or key not in store[client]:
        return None
    value = store[client][key]
    del store[client][key]
    if not store[client]:
        del store[client]
    return value


def guard(client, func, key, **kwargs):
    '''Retrieve the value for key from the stash. If it does not exist, call
    func to get a value. In either event re-stash the resulting value under the
    same key and return it.'''
    value = pop(client, key)
    if value is None:
        value = func(**kwargs)
    stash(client, key, value)
    return value


symbol_counter = 0


def symbol(pattern, default_tag='', tag=None):
    '''Allocate a symbol to be used in a template. This is useful for avoiding
    colliding with user symbols.'''
    global symbol_counter
    s = pattern % {
        'counter': symbol_counter,
        'tag': tag or default_tag,
    }
    symbol_counter += 1
    return s


def alloc_obj(client, space, name, type, label=None, **kwargs):
    '''Guarded allocation of an object. That is, if the object we're trying to
    allocate already exists, just return it. Otherwise allocate and save the
    object.'''
    return guard(client, space.alloc, '%s_obj' % name, type=type, name=name,
                 label=label, **kwargs)


def alloc_cap(client, space, name, obj, **kwargs):
    '''Guarded cap allocation. Works similarly to alloc_obj above.'''
    cap = guard(client, space.alloc, '%s_cap' % name, name=name, obj=obj, **kwargs)

    if obj is None:
        # The caller was allocating a free slot. No rights are relevant.
        return cap

    # Upgrade the cap's rights if required. This can occur in a situation where
    # we have connected an outgoing interface of a component instance to an
    # incoming interface of the same component. alloc will be called twice on
    # the EP with different permissions and we want to take the union of them.
    if not space.cnode[cap].read and kwargs.get('read', False):
        space.cnode[cap].read = True
    if not space.cnode[cap].write and kwargs.get('write', False):
        space.cnode[cap].write = True
    if not space.cnode[cap].grant and kwargs.get('grant', False):
        space.cnode[cap].grant = True
    if not space.cnode[cap].grantreply and kwargs.get('grantreply', False):
        space.cnode[cap].grantreply = True

    return cap


def calc_frame_size(size, frame_size, arch):
    if not frame_size:
        for sz in reversed(page_sizes(arch)):
            if size >= sz and size % sz == 0:
                frame_size = sz
                break
    assert frame_size, "Shared variable size: %d is not a valid page size multiple" % size
    return frame_size


def register_shared_variable(addr_space, obj_space, global_name, symbol, size, cap_space,
                             frame_size=None, paddr=None, perm='RWX', cached=True, label=None, with_mapping_caps=None):
    '''
    Create a reservation for a shared memory region between multiple
    components.

    global_name:   a global key that is used to link up the reservations
                   across multiple components.
    symbol:        the name of the local symbol to be backed by the
                   mapping frames.
    size:          the size of the region. Needs to be a multiple of the
                   smallest page size.
    cap_space:     the component's cspace. This is potentially used if the mapping caps
                   need to be moved to the component. In this case, with_mapping_caps needs
                   to be set when register_shared_variable is called.
    frame_size:    the size of frames to use to back the region. `size`
                   must be a multiple of `frame_size`. If `frame_size`
                   is not specified, the largest frame size that divides
                   evenly into `size` will be used.
    paddr:         the starting physical address of the frames. Only one
                   caller needs to specify this. If multiple callers
                   specify different values, the result is undefined.
    perm, cached:  page mapping options. These are only applied to the
                   caller's mapping
    label:         integrity label of the frame objects. In the default
                   `Context`, this defaults to the current entity name.
    with_mapping_caps: An array to return mapping caps if the component needs the
                   caps for the mapping to be moved into their own cspace.
    '''
    assert addr_space
    size = int(size)
    frame_size = calc_frame_size(size, frame_size, obj_space.spec.arch)
    num_frames = size//frame_size

    # If these frames have been allocated already then the allocator will return them.
    # Therefore calls to register_shared_variable with the same global_name have to have the same size.
    frames = [obj_space.alloc(ObjectType.seL4_FrameObject,
                              name='%s_%d_obj' % (global_name, i),
                              size=frame_size,
                              label=label)
              for i in range(num_frames)]
    if paddr is not None:
        for f in frames:
            f.paddr = paddr
            paddr += frame_size

    read = 'R' in perm
    write = 'W' in perm
    grant = 'X' in perm

    if with_mapping_caps is not None:
        # If we need the caps in our cspace, then we need to allocate them and call set_mapping_deferred on the cap
        # set_mapping_deferred will result in the correct mapping info being set when the spec is being generated.
        slots = [cap_space.alloc(frame, read=read, write=write, grant=grant,
                                 cached=cached) for frame in frames]
        caps = [cap_space.cnode[slot] for slot in slots]
        [cap.set_mapping_deferred() for cap in caps]
        with_mapping_caps.extend(slots)
    else:
        caps = [Cap(frame, read=read, write=write, grant=grant, cached=cached) for frame in frames]
    sizes = [frame_size] * num_frames
    addr_space.add_symbol_with_caps(symbol, sizes, caps)
    # Return code to:
    #  1. page-align the shared variable;
    #  2. make it visible in the final ELF; and
    #  3. Check that it is page-sized.
    return 'extern typeof(%(sym)s) %(sym)s ALIGN(%(frame_size)d) VISIBLE;\n'      \
           'static_assert(sizeof(%(sym)s) <= %(size)d,\n'                       \
           '  "typeof(%(sym)s) size greater than dataport size.");\n'                    \
           'static_assert(sizeof(%(sym)s) %% %(frame_size)d == 0,\n'              \
           '  "%(sym)s not page-sized. Template bug in its declaration? '       \
           'Suggested formulation: `char %(sym)s[ROUND_UP_UNSAFE(sizeof(...), ' \
           'PAGE_SIZE_4K)];`");' % {'sym': symbol, 'size': size, 'frame_size': frame_size}


def get_shared_variable_backing_frames(obj_space, global_name, size, frame_size=None, label=None):
    '''
    Return the objects for the frame mapping.
    global_name, size and frame_size need to be the same as was provided to register_shared_variable
    It is possible to call this in a component that does not call register_shared_variable if the component
    doesn't want a mapping itself, but requires caps for its cspace.
    '''
    size = int(size)
    frame_size = calc_frame_size(size, frame_size, obj_space.spec.arch)
    num_frames = size//frame_size
    return [obj_space.alloc(ObjectType.seL4_FrameObject,
                            name='%s_%d_obj' % (global_name, i),
                            size=frame_size,
                            label=label)
            for i in range(num_frames)]


def register_fill_frame(addr_space, symbol, fill, size, obj_space, label):
    '''
    Take a symbol and create a collection of 4K frames that can comfortably store 
    a region in the bootinfo.

    Return a static_assert checking that the symbol is of the correct size
    '''
    assert addr_space
    number_frames = size//4096
    frames = []
    for i in range(number_frames):
        fill_str = ['%d %d %s %d' % (0, 4096 if (size - (i * 4096)) >=
                                     4096 else (size - (i * 4096)), fill, i * 4096)]
        name = '%s_%s_%d_obj' % (symbol, label, i)
        frames.append(obj_space.alloc(ObjectType.seL4_FrameObject,
                                      name=name, label=label, fill=fill_str, size=4096))
    caps = [Cap(frame, read=True, write=False, grant=False) for frame in frames]
    sizes = [4096] * number_frames
    addr_space.add_symbol_with_caps(symbol, sizes, caps)
    return 'static_assert(sizeof(%(sym)s) == %(size)s,\n'           \
           ' "%(sym)s not page sized. Templage bug in its declaration?");'  \
           % {'sym': symbol, 'size': size}


def register_stack_symbol(addr_space, symbol, size, obj_space, label):
    '''
    Create a stack of `size` with a guard page on each side. This allocates the frames internally
    from the obj_space that is passed in as the frame objects shouldn't be needed anywhere else.
    Stack frames are read, write mappings.
    '''
    assert addr_space
    number_frames = size//4096
    frames = [obj_space.alloc(ObjectType.seL4_FrameObject, name='stack_%s_%d_%s_obj' % (symbol, i, label), label=label, size=4096)
              for i in range(number_frames)]
    # We create 2 additional mappings with None caps that are for the guard pages.
    sizes = [4096] * (number_frames + 2)
    caps = [None] + [Cap(frame, read=True, write=True, grant=False) for frame in frames] + [None]
    addr_space.add_symbol_with_caps(symbol, sizes, caps)


def register_ipc_symbol(addr_space, symbol, frame):
    '''
    Register an IPC buffer symbol with a cap to the frame that is passed in.
    The frame needs to be passed in instead of allocated internally because caps
    to the frame are needed by other objects such as the TCB for the thread.
    It is left to the caller to manage references to the Frame passed in.
    '''
    assert addr_space
    # We create 3*4K mappings with None on each side of the IPC buffer for guard pages
    caps = [None, Cap(frame, read=True, write=True, grant=False), None]
    sizes = [4096] * 3
    addr_space.add_symbol_with_caps(symbol, sizes, caps)


def register_dma_pool(addr_space, symbol, page_size, caps, cap_space):
    '''
    Register a DMA pool symbol region in the AddressSpaceAllocator.
    We pass in a list of slots and a cap_space allocator with the page size
    to specify the size and caps of the DMA region.
    '''
    assert addr_space
    addr_space.add_symbol_with_caps(
        symbol, [page_size] * len(caps), [cap_space.cnode[i] for i in caps])


def object_label_mapping(obj_space):
    '''Return a list of all objects and the integrity labels for them.'''
    return ((obj, label)
            for label, objs in obj_space.labels.items()
            for obj in objs)
