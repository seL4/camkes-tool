#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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
import capdl, code, collections, copy, inspect, itertools, functools, numbers, \
    orderedset, os, pdb, re, six, sys, textwrap

from capdl.Allocator import seL4_TCBObject, seL4_EndpointObject, \
    seL4_NotificationObject, seL4_CanRead, seL4_CanWrite, seL4_AllRights, \
    seL4_ARM_SmallPageObject, seL4_FrameObject, seL4_IRQControl, \
    seL4_UntypedObject, seL4_IA32_IOPort, seL4_IA32_IOSpace, \
    seL4_ARM_SectionObject, seL4_ARM_SuperSectionObject, \
    seL4_SchedContextObject

# Depending on what kernel branch we are on, we may or may not have ASIDs.
# There are separate python-capdl branches for this, but this import allows us
# to easily interoperate with both.
try:
    from capdl.Allocator import seL4_ASID_Pool
except ImportError:
    seL4_ASID_Pool = None

import camkes.ast as AST
from camkes.internal.Counter import Counter
from camkes.internal.version import version
from camkes.templates import macros, TemplateError
from .NameMangling import TEMPLATES, FILTERS, Perspective

def new_context(entity, assembly, obj_space, cap_space, shmem, **kwargs):
    '''Create a new default context for rendering.'''
    return dict(list(__builtins__.items()) + list({
        # Kernel object allocator
        'alloc_obj':(lambda name, type, **kwargs:
            alloc_obj((entity.label(), obj_space), obj_space,
                '%s_%s' % (entity.label(), name), type, label=entity.label(), **kwargs))
                    if obj_space else None,
        'seL4_EndpointObject':seL4_EndpointObject,
        'seL4_NotificationObject':seL4_NotificationObject,
        'seL4_TCBObject':seL4_TCBObject,
        'seL4_ARM_SmallPageObject':seL4_ARM_SmallPageObject,
        'seL4_ARM_SectionObject':seL4_ARM_SectionObject,
        'seL4_ARM_SuperSectionObject':seL4_ARM_SuperSectionObject,
        'seL4_FrameObject':seL4_FrameObject,
        'seL4_UntypedObject':seL4_UntypedObject,
        'seL4_IA32_IOPort':seL4_IA32_IOPort,
        'seL4_IA32_IOSpace':seL4_IA32_IOSpace,
        'seL4_SchedContextObject':seL4_SchedContextObject,
        'seL4_ASID_Pool':seL4_ASID_Pool,

        # Cap allocator
        'alloc_cap':(lambda name, obj, **kwargs:
            alloc_cap((entity.label(), cap_space), cap_space, name, obj, **kwargs)) \
                if cap_space else None,
        'seL4_CanRead':seL4_CanRead,
        'seL4_CanWrite':seL4_CanWrite,
        'seL4_AllRights':seL4_AllRights,
        'seL4_IRQControl':seL4_IRQControl,

        # The CNode root of your CSpace. Should only be necessary in cases
        # where you need to allocate a cap to it.
        'my_cnode':cap_space.cnode if cap_space is not None else None,

        # Batched object and cap allocation for when you don't need a reference
        # to the object. Probably best not to look directly at this one. When
        # you see `set y = alloc('foo', bar, moo)` in template code, think:
        #  set x = alloc_obj('foo_obj', bar)
        #  set y = alloc_cap('foo_cap', x, moo)
        'alloc':(lambda name, type, **kwargs:
            alloc_cap((entity.label(), cap_space), cap_space, name,
            alloc_obj((entity.label(), obj_space), obj_space,
                '%s_%s' % (entity.label(), name), type, label=entity.label(),
                **kwargs),
                **kwargs)) if cap_space else None,

        # Functionality for templates to inform us that they've emitted a C
        # variable that's intended to map to a shared variable. It is
        # (deliberately) left to the template authors to ensure global names
        # (gnames) only collide when intended; i.e. when they should map to the
        # same shared variable. The local name (lname) will later be used by us
        # to locate the relevant ELF frame(s) to remap. Note that we assume
        # address spaces and CSpaces are 1-to-1.
        'register_shared_variable':None if cap_space is None else \
            (lambda gname, lname, perm='RWX', paddr=None:
                register_shared_variable(shmem, gname, cap_space.cnode.name,
                    lname, perm, paddr)),

        # A `self`-like reference to the current AST object. It would be nice
        # to actually call this `self` to lead to more pythonic templates, but
        # `self` inside template blocks refers to the jinja2 parser.
        'me':entity,

        # The AST assembly's configuration.
        'configuration':assembly.configuration,

        # The AST assembly's composition
        'composition':assembly.composition,

        # Shared memory metadata. Templates should only need to modify this if
        # they're doing something cross-component.
        'shmem':shmem if entity is not None else None,

        # Cross-template variable passing helpers. These are quite low-level.
        # Avoid calling them unless necessary.
        'stash':partial(stash, entity.label()),
        'pop':partial(pop, entity.label()),
        'guard':partial(guard, entity.label()),

        # If the previous group of functions are considered harmful, these are
        # to be considered completely off limits. These expose a mechanism for
        # passing data between unrelated templates (_stash and _pop) and a way
        # of running arbitrary Python statements and expressions. They come
        # with significant caveats. E.g. _stash and _pop will likely not behave
        # as expected with the template cache enabled.
        '_stash':partial(stash, ''),
        '_pop':partial(pop, ''),
        'exec':_exec,

        # Helpers for creating unique symbols within templates.
        'c_symbol':partial(symbol, '_camkes_%(tag)s_%(counter)d'),
        'isabelle_symbol':partial(symbol, '%(tag)s%(counter)d\'', 's'),

        # Expose some library functions
        'assert':_assert,
        'itertools':itertools,
        'functools':functools,
        'lambda':lambda s: eval('lambda %s' % s),
        'numbers':numbers,
        'os':os,
        'pdb':pdb,
        'raise':_raise,
        're':re,
        'six':six,
        'set':orderedset.OrderedSet,
        'textwrap':textwrap,
        'copy':copy,
        'zip':zip,

        # Allocation pools. In general, do not touch these in templates, but
        # interact with them through the alloc* functions. They are only in the
        # context to allow unanticipated template extensions.
        'obj_space':obj_space,
        'cap_space':cap_space,

        # Debugging functions
        'breakpoint':_breakpoint,
        'sys':sys,

        # Work around for Jinja's bizarre scoping rules.
        'Counter':Counter,

        # Support for name mangling in the templates. See existing usage for
        # examples.
        'Perspective':lambda **kwargs:Perspective(TEMPLATES, **kwargs),

        # Low-level access to name mangling. Should only be required when you
        # need to access both mangling phases.
        'NameMangling':collections.namedtuple('NameMangling',
            ['FILTERS', 'TEMPLATES', 'Perspective'])(FILTERS, TEMPLATES,
                Perspective),

        # Return a list of distinct elements. Normally you would just do this
        # as list(set(xs)), but this turns out to be non-deterministic in the
        # template environment for some reason.
        'uniq':lambda xs: reduce(lambda ys, z: ys if z in ys else (ys + [z]), xs, []),

        # Functional helpers.
        'flatMap':lambda f, xs: list(itertools.chain.from_iterable(map(f, xs))),
        'flatten':lambda xss: list(itertools.chain.from_iterable(xss)),

        # Macros for common operations.
        'macros':macros,

        # Give template authors access to AST types just in case. Templates
        # should never be constructing objects of these types, but they may
        # need to do `isinstance` testing.
        'camkes':collections.namedtuple('camkes', ['ast'])(AST),

        # Expose CapDL module for `isinstance` testing.
        'capdl':capdl,

        # Give the template authors a mechanism for writing C-style include
        # guards. Use the following idiom to guard an include target:
        #  /*- if 'template.filename' not in included' -*/
        #  /*- do included.add('template.filename') -*/
        #  ... my template ...
        #  /*- endif -*/
        'included':set(),

        # Expose an exception class templates can use to throw errors related
        # to invalid input specification.
        'TemplateError':TemplateError,

        # Version information. Templates are unlikely to depend on this, but we
        # emit it to give component instances a runtime-discoverable CAmkES
        # version.
        'camkes_version':version(),
    }.items()) + list(kwargs.items()))

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
        'banner':'Breakpoint triggered',
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
        'counter':symbol_counter,
        'tag':tag or default_tag,
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

    return cap

def register_shared_variable(shmem, global_name, local_context, local_name,
        permissions='RWX', paddr=None):
    '''Track a variable that is intended to map to a cross-address-space shared
    variable.
     shmem - The dictionary to use for tracking
     global_name - The system-wide name for this variable
     local_context - The owner's CNode name
     local_name - The name of this variable in the owner's address space
    '''
    shmem[global_name][local_context].append((local_name, permissions, paddr))

    # Return code to:
    #  1. page-align the shared variable;
    #  2. make it visible in the final ELF; and
    #  3. Check that it is page-sized.
    return 'extern typeof(%(sym)s) %(sym)s ALIGN(PAGE_SIZE_4K) VISIBLE;\n'      \
           'static_assert(sizeof(%(sym)s) %% PAGE_SIZE_4K == 0,\n'              \
           '  "%(sym)s not page-sized. Template bug in its declaration? '       \
           'Suggested formulation: `char %(sym)s[ROUND_UP_UNSAFE(sizeof(...), ' \
           'PAGE_SIZE_4K)];`");' % {'sym':local_name}
