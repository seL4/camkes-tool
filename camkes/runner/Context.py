#
# Copyright 2014, NICTA
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

from functools import partial
from copy import deepcopy
import code, collections, inspect, itertools, math, os, pdb, re, textwrap

from capdl.Allocator import seL4_TCBObject, seL4_EndpointObject, \
    seL4_AsyncEndpointObject, seL4_CanRead, seL4_CanWrite, seL4_AllRights, \
    seL4_ARM_SmallPageObject, seL4_FrameObject, seL4_IRQControl, \
    seL4_UntypedObject, seL4_IA32_IOPort, seL4_IA32_IOSpace, \
    seL4_ARM_SectionObject, seL4_ARM_SuperSectionObject

# Depending on what kernel branch we are on, we may or may not have ASIDs.
# There are separate python-capdl branches for this, but this import allows us
# to easily interoperate with both.
try:
    from capdl.Allocator import seL4_ASID_Pool
except ImportError:
    seL4_ASID_Pool = None

import camkes.ast as AST
from camkes.internal.DeterministicSet import DeterministicSet
from camkes.internal.Counter import Counter
from camkes.templates import macros
from Joiner import Joiner
from apply import apply, by, done, oops, sorry
from NameMangling import TEMPLATES, FILTERS, Perspective

def new_context(entity, configuration, obj_space, cap_space, shmem, **kwargs):
    '''Create a new default context for rendering.'''
    return dict({
        # Kernel object allocator
        'alloc_obj':(lambda name, type, **kwargs:
            alloc_obj((entity, obj_space), obj_space,
                '%s_%s' % (entity.name, name), type, label=entity.name, **kwargs))
                    if obj_space else None,
        'seL4_EndpointObject':seL4_EndpointObject,
        'seL4_AsyncEndpointObject':seL4_AsyncEndpointObject,
        'seL4_TCBObject':seL4_TCBObject,
        'seL4_ARM_SmallPageObject':seL4_ARM_SmallPageObject,
        'seL4_ARM_SectionObject':seL4_ARM_SectionObject,
        'seL4_ARM_SuperSectionObject':seL4_ARM_SuperSectionObject,
        'seL4_FrameObject':seL4_FrameObject,
        'seL4_UntypedObject':seL4_UntypedObject,
        'seL4_IA32_IOPort':seL4_IA32_IOPort,
        'seL4_IA32_IOSpace':seL4_IA32_IOSpace,
        'seL4_ASID_Pool':seL4_ASID_Pool,

        # Cap allocator
        'alloc_cap':(lambda name, obj, **kwargs: \
            alloc_cap((entity, cap_space), cap_space, name, obj, **kwargs)) \
                if cap_space else None,
        'seL4_CanRead':seL4_CanRead,
        'seL4_CanWrite':seL4_CanWrite,
        'seL4_AllRights':seL4_AllRights,
        'seL4_IRQControl':seL4_IRQControl,

        # The CNode root of your CSpace. Should only be necessary in cases
        # where you need to allocate a cap to it.
        'my_cnode':cap_space.cnode if cap_space is not None else None,

        # Some C familiars.
        'PAGE_SIZE':4096,
        'ROUND_UP':lambda x, y: int(int(math.ceil(int(x) / float(y))) * y),
        '__WORDSIZE':32,
        '__SIZEOF_POINTER__':4,
        # Calculate the size of a type at template instantiation time. In
        # general, you should prefer emitting a call to C's sizeof over this
        # because it leads to more readable and portable output. This is only
        # provided for cases where you explicitly need to know the size of a
        # type ahead of compilation time.
        'sizeof':sizeof,

        # Batched object and cap allocation for when you don't need a reference
        # to the object. Probably best not to look directly at this one. When
        # you see `set y = alloc('foo', bar, moo)` in template code, think:
        #  set x = alloc_obj('foo_obj', bar)
        #  set y = alloc_cap('foo_cap', x, moo)
        'alloc':(lambda name, type, **kwargs:
            alloc_cap((entity, cap_space), cap_space, name,
            alloc_obj((entity, obj_space), obj_space,
                '%s_%s' % (entity.name, name), type, label=entity.name,
                **kwargs),
                **kwargs)) if cap_space else None,

        # Functionality for templates to inform us that they've emitted a C
        # variable that's intended to map to a shared variable. It is
        # (deliberately) left to the template authors to ensure global names
        # (gnames) only collide when intended; i.e. when they should map to the
        # same shared variable. The local name (lname) will later be used by us
        # to locate the relevant ELF frame(s) to remap.
        'register_shared_variable':(lambda gname, lname: \
            register_shared_variable(shmem, gname, entity.name, lname)),

        # A `self`-like reference to the current AST object. It would be nice
        # to actually call this `self` to lead to more pythonic templates, but
        # `self` inside template blocks refers to the jinja2 parser.
        'me':entity,

        # The AST assembly's configuration.
        'configuration':configuration,

        # Allow some AST objects to be printed trivially
        'show':show,

        # Cross-template variable passing helpers. These are quite low-level.
        # Avoid calling them unless necessary.
        'stash':partial(stash, entity),
        'pop':partial(pop, entity),
        'guard':partial(guard, entity),

        # If the previous group of functions are considered harmful, these are
        # to be considered completely off limits. These expose a mechanism for
        # passing data between unrelated templates (_stash and _pop) and a way
        # of running arbitrary Python statements and expressions. They come
        # with significant caveats. E.g. _stash and _pop will likely not behave
        # as expected with the template cache enabled.
        '_stash':partial(stash, ''),
        '_pop':partial(pop, ''),
        'exec':_exec,
        'eval':eval,

        # Helpers for creating unique symbols within templates.
        'c_symbol':partial(symbol, '_camkes_%(tag)s_%(counter)d'),
        'isabelle_symbol':partial(symbol, '%(tag)s%(counter)d\'', 's'),

        # Expose some library functions
        'assert':_assert,
        'bool':bool,
        'enumerate':enumerate,
        'Exception':Exception,
        'filter':filter,
        'float':float,
        'hex':hex,
        'int':int,
        'isinstance':isinstance,
        'lambda':lambda s: eval('lambda %s' % s),
        'len':len,
        'list':list,
        'map':map,
        'math':collections.namedtuple('math', ['pow'])(math.pow),
        'NotImplementedError':lambda x='NotImplementedError': NotImplementedError(x),
        'os':collections.namedtuple('os', ['path'])(os.path),
        'pdb':collections.namedtuple('pdb', ['set_trace'])(_set_trace),
        'raise':_raise,
        're':collections.namedtuple('re', ['sub', 'match'])(re.sub, re.match),
        'reduce':reduce,
        'reversed':reversed,
        'set':DeterministicSet,
        'str':str,
        'splitext':os.path.splitext,
        'arch':os.environ.get('ARCH', ''),
        'ord':ord,
        'chr':chr,
        'textwrap':collections.namedtuple('textwrap', ['wrap'])(textwrap.wrap),
        'copy':collections.namedtuple('copy', ['deepcopy'])(deepcopy),

        # Allocation pools. In general, do not touch these in templates, but
        # interact with them through the alloc* functions. They are only in the
        # context to allow unanticipated template extensions.
        'obj_space':obj_space,
        'cap_space':cap_space,

        # Debugging functions
        'breakpoint':_breakpoint,

        # Helper for generating lists.
        'Joiner':Joiner,

        # Work around for Jinja's bizarre scoping rules.
        'Counter':Counter,

        # Helper functions for generating apply-style Isabelle proof scripts.
        'apply':apply,
        'by':by,
        'done':done,
        'oops':oops,
        'sorry':sorry,

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

        # When generating Isabelle apply-style proof scripts, the results can
        # sometimes be fragile in the face of changing code. In particular,
        # sometimes a generated proof can fail because the underlying code
        # changed, but inadvertently make progress beyond the actual divergence
        # point, concealing the source of the failure. This function allows you
        # to assert within an apply-style proof what the current subgoal looks
        # like. The idea is that this step will fail early when the code
        # changes, giving you a better idea of where to begin repairing the
        # proof.
        'assert_current_goal':lambda prop:'apply (subgoal_tac "%s", assumption)' % prop \
            if kwargs['options'].verbosity >= 2 else '',

        # Give the template authors a mechanism for writing C-style include
        # guards. Use the following idiom to guard an include target:
        #  /*- if 'template.filename' not in included' -*/
        #  /*- do included.add('template.filename') -*/
        #  ... my template ...
        #  /*- endif -*/
        'included':set(),
    }.items() + kwargs.items())

def _assert(condition):
    '''Hack to reify assert as a callable'''
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
    exec statement in stack_frames[caller][0].f_globals, \
        stack_frames[caller][0].f_locals
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

def _set_trace():
    '''Wrap PDB's set_trace so that you can use it inside a /*? ?*/ block.'''
    pdb.set_trace()
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

def show(obj):
    '''Short smattering of logic for showing AST objects in C. This would be
    nicer to do as a template macro, but becomes cumbersome thanks to the
    inability to nest macros or call out to context functions.'''
    if isinstance(obj, AST.Reference):
        return obj._symbol
    elif isinstance(obj, AST.Type):
        if obj.type == 'string':
            return 'char *'
        elif obj.type == 'character':
            return 'char'
        elif obj.type == 'boolean':
            return 'bool'
        else:
            return obj.type
    elif isinstance(obj, AST.Direction):
        if obj.direction in ['inout', 'out']:
            return '*'
        else:
            return ''
    elif isinstance(obj, AST.Parameter):
        return '%(size)s %(type)s %(pointer)s %(array)s %(name)s' % \
            {'size':('size_t %(ptr)s%(name)s_sz,' % {
                'name':obj.name,
                'ptr':show(obj.direction),
             }) if obj.array else '',
             'type':show(obj.type),
             'pointer':show(obj.direction),
             'name':obj.name,
             'array':'*' if obj.array else ''}
    else:
        raise NotImplementedError

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

def register_shared_variable(shmem, global_name, local_context, local_name):
    '''Track a variable that is intended to map to a cross-address-space shared
    variable.
     shmem - The dictionary to use for tracking
     global_name - The system-wide name for this variable
     local_context - The caller's identifying name
     local_name - The name of this variable in the caller's address space
    '''
    if global_name not in shmem:
        shmem[global_name] = {}
    shmem[global_name][local_context] = local_name
    return ''

# XXX: Types should really be modelled in a cleaner way so we know their size
# without this hack.
# XXX: Assumes 32-bit platform.
def sizeof(t):
    if isinstance(t, AST.Parameter):
        return sizeof(t.type)

    # HACK: We want to be able to call sizeof on Buf dataports. We should have
    # a more principled way of doing this.
    if isinstance(t, AST.Reference) and t._symbol == 'Buf':
        return 4096

    assert isinstance(t, AST.Type)
    if t.type in ['int64_t', 'uint64_t', 'double']:
        return 8
    elif t.type in ['int', 'unsigned int', 'int32_t', 'uint32_t', 'float', 'uintptr_t']:
        return 4
    elif t.type in ['int16_t', 'uint16_t']:
        return 2
    elif t.type in ['int8_t', 'uint8_t', 'char', 'character', 'boolean']:
        return 1
    else:
        raise NotImplementedError
