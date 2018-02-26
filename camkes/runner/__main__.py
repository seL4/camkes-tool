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

'''Entry point for the runner (template instantiator).'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

# Excuse this horrible prelude. When running under a different interpreter we
# have an import path that doesn't include dependencies like elftools and
# Jinja. We need to juggle the import path prior to importing them. Note, this
# code has no effect when running under the standard Python interpreter.
import platform, subprocess, sys
if platform.python_implementation() != 'CPython':
    path = eval(subprocess.check_output(['python', '-c',
        'import sys; sys.stdout.write(\'%s\' % sys.path)'],
        universal_newlines=True))
    for p in path:
        if p not in sys.path:
            sys.path.append(p)

from camkes.ast import ASTError, Connection, Connector
from camkes.templates import Templates, PLATFORMS, TemplateError
from camkes.internal.cachea import Cache as LevelACache, \
    prime_inputs as level_a_prime
from camkes.internal.cacheb import Cache as LevelBCache, \
    prime_ast_hash as level_b_prime
import camkes.internal.log as log
from camkes.internal.version import sources, version
from camkes.internal.exception import CAmkESError
from camkes.runner.NameMangling import Perspective, RUNNER
from camkes.runner.Renderer import Renderer
from camkes.runner.Filters import CAPDL_FILTERS

import argparse, collections, functools, jinja2, locale, numbers, os, re, \
    six, sqlite3, string, traceback, pickle, errno
from capdl import seL4_CapTableObject, ObjectAllocator, CSpaceAllocator, \
    ELF, lookup_architecture

from camkes.parser import parse_file, ParseError

CAPDL_STATE_PICKLE = 'capdl_state.p'

class ParserOptions():
    def __init__(self, cpp, cpp_flag, import_path, verbosity, allow_forward_references):
        self.cpp = cpp
        self.cpp_flag = cpp_flag
        self.import_path = import_path
        self.verbosity = verbosity
        self.allow_forward_references = allow_forward_references

class FilterOptions():
    def __init__(self, architecture, realtime, largeframe, largeframe_dma, default_priority,
            default_max_priority, default_criticality, default_max_criticality, default_affinity,
            default_period, default_budget, default_data, default_size_bits, debug_fault_handlers,
            fprovide_tcb_caps):
        self.architecture = architecture
        self.realtime = realtime
        self.largeframe = largeframe
        self.largeframe_dma = largeframe_dma
        self.default_priority = default_priority
        self.default_max_priority = default_max_priority
        self.default_criticality = default_criticality
        self.default_max_criticality = default_max_criticality
        self.default_affinity = default_affinity
        self.default_period = default_period
        self.default_budget = default_budget
        self.default_data = default_data
        self.default_size_bits = default_size_bits
        self.debug_fault_handlers = debug_fault_handlers
        self.fprovide_tcb_caps = fprovide_tcb_caps

def safe_decode(s):
    '''
    Safely extract a string that may contain invalid character encodings.

    When formatting a traceback that crosses a boundary between compiled and
    interpreted code, the backtracer can lose the frame pointer and start
    appending garbage to the traceback. If we try to print this we trigger a
    UnicodeDecodeError. To avoid this, wrap traceback printing in this
    function.
    '''
    r = []
    for c in s:
        if c not in string.printable:
            r.append('\n  <MALFORMED BYTES>\n')
            break
        r.append(c)
    return ''.join(r)

def _die(options, message):

    if isinstance(message, (list, tuple)):
        for line in message:
            log.error(line)
    else:
        log.error(message)

    tb = traceback.format_exc()
    log.debug('\n --- Python traceback ---\n%s ------------------------\n' %
        safe_decode(tb))
    if options.cache and re.search(r'^\s*File\s+".*\.pyc",\s+line\s+\d+,\s*in'
            r'\s*top-level\s*template\s*code$', tb, flags=re.MULTILINE) is \
            not None:
        log.debug('If the preceding backtrace traverses a pre-compiled '
            'template, you may wish to disable the CAmkES cache and re-run '
            'for a more accurate backtrace.\n')
    sys.exit(-1)

def parse_args(argv, out, err):
    parser = argparse.ArgumentParser(prog='python -m camkes.runner',
        description='instantiate templates based on a CAmkES specification')
    parser.add_argument('--file', '-f', help='Add this file to the list of '
        'input files to parse. Files are parsed in the order in which they are '
        'encountered on the command line.', type=argparse.FileType('r'),
        required=True)
    parser.add_argument('--cpp', action='store_true', help='Pre-process the '
        'source with CPP')
    parser.add_argument('--nocpp', action='store_false', dest='cpp',
        help='Do not pre-process the source with CPP')
    parser.add_argument('--cpp-flag', action='append', default=[],
        help='Specify a flag to pass to CPP')
    parser.add_argument('--import-path', '-I', help='Add this path to the list '
        'of paths to search for built-in imports. That is, add it to the list '
        'of directories that are searched to find the file "foo" when '
        'encountering an expression "import <foo>;".', action='append',
        default=[])
    parser.add_argument('--quiet', '-q', help='No output.', dest='verbosity',
        default=1, action='store_const', const=0)
    parser.add_argument('--verbose', '-v', help='Verbose output.',
        dest='verbosity', action='store_const', const=2)
    parser.add_argument('--debug', '-D', help='Extra verbose output.',
        dest='verbosity', action='store_const', const=3)
    parser.add_argument('--outfile', '-O', help='Output to the given file.',
        type=argparse.FileType('w'), required=True)
    parser.add_argument('--elf', '-E', help='ELF files to contribute to a '
        'CapDL specification.', action='append', default=[])
    parser.add_argument('--item', '-T', help='AST entity to produce code for.',
        required=True)
    parser.add_argument('--platform', '-p', help='Platform to produce code '
        'for. Pass \'help\' to see valid platforms.', default='seL4',
        choices=PLATFORMS)
    parser.add_argument('--templates', '-t', help='Extra directories to '
        'search for templates (before builtin templates).', action='append',
        default=[])
    parser.add_argument('--cache', '-c', action='store_true',
        help='Enable code generation cache.')
    parser.add_argument('--cache-dir',
        default=os.path.expanduser('~/.camkes/cache'),
        help='Set code generation cache location.')
    parser.add_argument('--version', action='version', version='%s %s' %
        (argv[0], version()))
    parser.add_argument('--frpc-lock-elision', action='store_true',
        default=True, help='Enable lock elision optimisation in seL4RPC '
        'connector.')
    parser.add_argument('--fno-rpc-lock-elision', action='store_false',
        dest='frpc_lock_elision', help='Disable lock elision optimisation in '
        'seL4RPC connector.')
    parser.add_argument('--fspecialise-syscall-stubs', action='store_true',
        default=True, help='Generate inline syscall stubs to reduce overhead '
        'where possible.')
    parser.add_argument('--fno-specialise-syscall-stubs', action='store_false',
        dest='fspecialise_syscall_stubs', help='Always use the libsel4 syscall '
        'stubs.')
    parser.add_argument('--fprovide-tcb-caps', action='store_true',
        default=True, help='Hand out TCB caps to components, allowing them to '
        'exit cleanly.')
    parser.add_argument('--fno-provide-tcb-caps', action='store_false',
        dest='fprovide_tcb_caps', help='Do not hand out TCB caps, causing '
        'components to fault on exiting.')
    parser.add_argument('--fsupport-init', action='store_true', default=True,
        help='Support pre_init, post_init and friends.')
    parser.add_argument('--fno-support-init', action='store_false',
        dest='fsupport_init', help='Do not support pre_init, post_init and '
        'friends.')
    parser.add_argument('--default-priority', type=int, default=254,
        help='Default component thread priority.')
    parser.add_argument('--default-max-priority', type=int, default=254,
        help='Default component thread maximum priority.')
    parser.add_argument('--default-criticality', type=int, default=1,
        help='Default component thread criticality.')
    parser.add_argument('--default-max-criticality', type=int, default=1,
        help='Default component thread maximum criticality.')
    parser.add_argument('--default-affinity', type=int, default=0,
        help='Default component thread affinity.')
    parser.add_argument('--default-period', type=int, default=10000,
        help='Default component thread scheduling context period.')
    parser.add_argument('--default-budget', type=int, default=10000,
        help='Default component thread scheduling context budget.')
    parser.add_argument('--default-data', type=int, default=0,
        help='Default component thread scheduling context data.')
    parser.add_argument('--default-size_bits', type=int, default=8,
        help='Default scheduling context size bits.')
    parser.add_argument('--prune', action='store_true',
        help='Minimise the number of functions in generated C files.')
    parser.add_argument('--largeframe', action='store_true',
        help='Try to use large frames when possible.')
    parser.add_argument('--architecture', '--arch', default='aarch32',
        type=lambda x: type('')(x).lower(), choices=('aarch32', 'arm_hyp', 'ia32', 'x86_64'),
        help='Target architecture.')
    parser.add_argument('--makefile-dependencies', '-MD',
        type=argparse.FileType('w'), help='Write Makefile dependency rule to '
        'FILE')
    parser.add_argument('--allow-forward-references', action='store_true',
        help='allow refering to objects in your specification that are '
        'defined after the point at which they are referenced')
    parser.add_argument('--disallow-forward-references', action='store_false',
        dest='allow_forward_references', help='only permit references in '
        'specifications to objects that have been defined before that point')
    parser.add_argument('--debug-fault-handlers', action='store_true',
        help='provide fault handlers to decode cap and VM faults for the '
        'purposes of debugging')
    parser.add_argument('--largeframe-dma', action='store_true',
        help='promote frames backing DMA pools to large frames where possible')
    parser.add_argument('--realtime', action='store_true',
        help='Target realtime seL4.')
    parser.add_argument('--data-structure-cache-dir', type=str,
        help='Directory for storing pickled datastructures for re-use between multiple '
             'invocations of the camkes tool in a single build. The user should delete '
             'this directory between builds.')

    # Juggle the standard streams either side of parsing command-line arguments
    # because argparse provides no mechanism to control this.
    old_out = sys.stdout
    old_err = sys.stderr
    sys.stdout = out
    sys.stderr = err
    options = parser.parse_args(argv[1:])
    sys.stdout = old_out
    sys.stderr = old_err

    return options

def pickle_call(data_structure_cache_dir, pickle_name, fn, *args, **kwargs):
    cache_path = os.path.realpath(data_structure_cache_dir)
    pickle_path = os.path.join(cache_path, pickle_name)

    try:
        if not os.path.isdir(cache_path):
            os.makedirs(cache_path)

        with open(pickle_path, 'rb') as pickle_file:
            return pickle.load(pickle_file)

    except IOError as e:
        result = fn(*args, **kwargs)
        if e.args[0] == errno.ENOENT:
            # pickled file doesn't exist yet - create it
            with open(pickle_path, 'wb') as pickle_file:
                pickle.dump(result, pickle_file)

        return result

    except Exception:
        # fall back to calling the function without pickling
        return fn(*args, **kwargs)

def parse_file_cached(filename, data_structure_cache_dir, parser_options):
    if data_structure_cache_dir is None:
        return parse_file(filename, kwargs)

    return pickle_call(data_structure_cache_dir, 'ast.p', parse_file, filename, parser_options)

class ShmemFactory:
    '''Factory supplied to the shared memory allocator's defaultdict.
       A callable class is used instead of a lambda to simplify serializing.'''
    def __call__(self):
        return collections.defaultdict(list)

def main(argv, out, err):

    # We need a UTF-8 locale, so bail out if we don't have one. More
    # specifically, things like the version() computation traverse the file
    # system and, if they hit a UTF-8 filename, they try to decode it into your
    # preferred encoding and trigger an exception.
    encoding = locale.getpreferredencoding().lower()
    if encoding not in ('utf-8', 'utf8'):
        err.write('CAmkES uses UTF-8 encoding, but your locale\'s preferred '
            'encoding is %s. You can override your locale with the LANG '
            'environment variable.\n' % encoding)
        return -1

    options = parse_args(argv, out, err)

    # Save us having to pass debugging everywhere.
    die = functools.partial(_die, options)

    log.set_verbosity(options.verbosity)

    cwd = os.getcwd()

    # Construct the compilation caches if requested.
    cachea = None
    cacheb = None
    if options.cache:

        # Construct a modified version of the command line arguments that we'll
        # use in the keys to the caches. Essentially we elide --outfile and its
        # parameter under the assumption that this value is never used in code
        # generation. The purpose of this is to allow us to successfully cache
        # ancillary outputs that we generate along the way to the current
        # output. If we were to include --outfile in the key, future attempts
        # to generate these ancillary outputs would unnecessarily miss the
        # entries generated by this execution.
        args = []
        skip = False
        for index, arg in enumerate(argv[1:]):
            if skip:
                skip = False
                continue
            if arg in ('--outfile', '-O'):
                skip = True
                continue
            args.append(arg)

        cachea = LevelACache(os.path.join(options.cache_dir, version(), 'cachea'))
        cacheb = LevelBCache(os.path.join(options.cache_dir, version(), 'cacheb'))

    def done(s):
        ret = 0
        if s:
            options.outfile.write(s)
            options.outfile.close()
        if cachea is not None:
            try:
                cachea.flush()
            except sqlite3.OperationalError as e:
                # The following suppresses two spurious errors:
                #  1. The database is locked. In a large, parallel build, writes
                #     to the level A cache are heavily contended and this error
                #     can occur.
                #  2. The database structure is unexpected. If the CAmkES
                #     sources have changed *while* the runner was executing,
                #     the level A cache can be looking in a different place to
                #     where the cache was created.
                # Both of these are non-critical (will just result in a
                # potential future cache miss) so there's no need to alarm the
                # user.
                if re.search(r'database is locked', str(e)) is not None or \
                   re.search(r'no such table', str(e)) is not None:
                    log.debug('failed to flush level A cache: %s' % str(e))
                else:
                    raise
        if cacheb is not None:
            try:
                cacheb.flush()
            except sqlite3.OperationalError as e:
                # As above for the level B cache.
                if re.search(r'database is locked', str(e)):
                    log.debug('failed to flush level B cache: %s' % str(e))
                else:
                    raise
        sys.exit(ret)

    # Try to find this output in the level A cache if possible. This check will
    # 'hit' if the source files representing the input spec are identical to
    # some previously observed execution.
    if cachea is not None:
        assert 'args' in locals()
        output = cachea.load(args, cwd)
        if output is not None:
            log.debug('Retrieved %(platform)s/%(item)s from level A cache' %
                options.__dict__)
            done(output)

    filename = os.path.abspath(options.file.name)

    try:
        # Build the parser options
        parse_options = ParserOptions(options.cpp, options.cpp_flag, options.import_path, options.verbosity, options.allow_forward_references)
        ast, read = parse_file_cached(filename, options.data_structure_cache_dir, parse_options)
    except (ASTError, ParseError) as e:
        die(e.args)

    # Locate the assembly.
    assembly = ast.assembly
    if assembly is None:
        die('No assembly found')

    # Do some extra checks if the user asked for verbose output.
    if options.verbosity >= 2:

        # Try to catch type mismatches in attribute settings. Note that it is
        # not possible to conclusively evaluate type correctness because the
        # attributes' type system is (deliberately) too loose. That is, the
        # type of an attribute can be an uninterpreted C type the user will
        # provide post hoc.
        for i in assembly.composition.instances:
            for a in i.type.attributes:
                value = assembly.configuration[i.name].get(a.name)
                if value is not None:
                    if a.type == 'string' and not \
                            isinstance(value, six.string_types):
                        log.warning('attribute %s.%s has type string but is '
                            'set to a value that is not a string' % (i.name,
                            a.name))
                    elif a.type == 'int' and not \
                            isinstance(value, numbers.Number):
                        log.warning('attribute %s.%s has type int but is set '
                            'to a value that is not an integer' % (i.name,
                                a.name))

    obj_space = ObjectAllocator()
    obj_space.spec.arch = options.architecture
    cspaces = {}
    pds = {}
    conf = assembly.configuration
    shmem = collections.defaultdict(ShmemFactory())
    kept_symbols = {}
    fill_frames = {}

    templates = Templates(options.platform)
    [templates.add_root(t) for t in options.templates]
    try:
        r = Renderer(templates, options.cache, options.cache_dir)
    except jinja2.exceptions.TemplateSyntaxError as e:
        die('template syntax error: %s' % e)

    # The user may have provided their own connector definitions (with
    # associated) templates, in which case they won't be in the built-in lookup
    # dictionary. Let's add them now. Note, definitions here that conflict with
    # existing lookup entries will overwrite the existing entries. Note that
    # the extra check that the connector has some templates is just an
    # optimisation; the templates module handles connectors without templates
    # just fine.
    extra_templates = set()
    for c in (x for x in ast.items if isinstance(x, Connector) and
            (x.from_template is not None or x.to_template is not None)):
        try:
            # Find a connection that uses this type.
            connection = next(x for x in ast if isinstance(x, Connection) and
                x.type == c)
            # Add the custom templates and update our collection of read
            # inputs. It is necessary to update the read set here to avoid
            # false compilation cache hits when the source of a custom template
            # has changed.
            extra_templates |= templates.add(c, connection)
        except TemplateError as e:
            die('while adding connector %s: %s' % (c.name, e))
        except StopIteration:
            # No connections use this type. There's no point adding it to the
            # template lookup dictionary.
            pass

    # Check if our current target is in the level B cache. The level A cache
    # will 'miss' and this one will 'hit' when the input spec is identical to
    # some previously observed execution modulo a semantically irrelevant
    # element (e.g. an introduced comment).
    ast_hash = None
    if cacheb is not None:
        ast_hash = level_b_prime(ast)
        assert 'args' in locals()
        output = cacheb.load(ast_hash, args, set(options.elf) | extra_templates)
        if output is not None:
            log.debug('Retrieved %(platform)s/%(item)s from level B cache' %
                options.__dict__)
            done(output)

    # Add custom templates.
    read |= extra_templates

    # Add the CAmkES sources themselves to the accumulated list of inputs.
    read |= set(path for path, _ in sources())

    # Add any ELF files we were passed as inputs.
    read |= set(options.elf)

    # Write a Makefile dependency rule if requested.
    if options.makefile_dependencies is not None:
        options.makefile_dependencies.write('%s: \\\n  %s\n' %
            (filename, ' \\\n  '.join(sorted(read))))

    # If we have a cache, allow outputs to be saved to it.
    if options.cache:

        assert cachea is not None, 'level A cache not available, though the ' \
            'cache is enabled (bug in runner?)'

        # Calculate the input files to the level A cache.
        inputs = level_a_prime(read)

        # Work out the position of the --item argument in the command line
        # parameters. We will use this to cache not only outputs for this
        # execution, but also outputs for ones with a different target.
        item_index = None
        assert 'args' in locals()
        for index, arg in enumerate(args[:-1]):
            if arg in ('--item', '-T'):
                item_index = index + 1
                break
        assert item_index is not None, 'failed to find required argument ' \
            '--item (bug in runner?)'

        # We should already have the necessary inputs for the level B cache.
        assert cacheb is not None, 'level B cache not available, though the ' \
            'cache is enabled (bug in runner?)'
        assert ast_hash is not None, 'AST hash not pre-computed (bug in ' \
            'runner?)'

        def save(item, value):
            # Juggle the command line arguments to cache the predicted
            # arguments for a call that would generate this item.
            new_args = args[:item_index] + [item] + args[item_index + 1:]

            # Save entries in both caches.
            cachea.save(new_args, cwd, value, inputs)
            if item != 'Makefile':
                # We avoid caching the generated Makefile because it is not
                # safe. The inputs to generation of the Makefile are not only
                # the AST, but also the file names (`inputs`). If we cache it in
                # the level B cache we risk the following scenario:
                #
                #   1. Generate the Makefile, caching it in the level B cache;
                #   2. Modify the spec to import a file containing only white
                #      space and/or comments; then
                #   3. Generate the Makefile, missing the level A cache, but
                #      hitting the level B cache.
                #
                # At this point, the generated Makefile is incorrect because it
                # does not capture any dependencies on the imported file. We can
                # now introduce something semantically relevant into this file
                # (e.g. an Assembly block) and it will not be seen by the build
                # system.
                cacheb.save(ast_hash, new_args,
                    set(options.elf) | extra_templates, value)
    else:
        def save(item, value):
            pass

    def apply_capdl_filters():
        # Derive a set of usable ELF objects from the filenames we were passed.
        elfs = {}
        for e in options.elf:
            try:
                name = os.path.basename(e)
                if name in elfs:
                    raise Exception('duplicate ELF files of name \'%s\' encountered' % name)
                elf = ELF(e, name, options.architecture)
                p = Perspective(phase=RUNNER, elf_name=name)
                group = p['group']
                # Avoid inferring a TCB as we've already created our own.
                elf_spec = elf.get_spec(infer_tcb=False, infer_asid=False,
                    pd=pds[group], use_large_frames=options.largeframe)
                obj_space.merge(elf_spec, label=group)
                elfs[name] = (e, elf)
            except Exception as inst:
                die('While opening \'%s\': %s' % (e, inst))

        # It's only relevant to run these filters if the final target is CapDL.
        # Note, this will no longer be true if we add any other templates that
        # depend on a fully formed CapDL spec. Guarding this loop with an if
        # is just an optimisation and the conditional can be removed if
        # desired.
        filteroptions = FilterOptions(options.architecture, options.realtime, options.largeframe,
            options.largeframe_dma, options.default_priority, options.default_max_priority,
            options.default_criticality, options.default_max_criticality, options.default_affinity,
            options.default_period, options.default_budget, options.default_data, options.default_size_bits,
            options.debug_fault_handlers, options.fprovide_tcb_caps)
        for f in CAPDL_FILTERS:
            try:
                # Pass everything as named arguments to allow filters to
                # easily ignore what they don't want.
                f(ast=ast, obj_space=obj_space, cspaces=cspaces, elfs=elfs,
                    options=filteroptions, shmem=shmem, fill_frames=fill_frames)
            except Exception as inst:
                die('While forming CapDL spec: %s' % inst)

    def instantiate_misc_template():
        try:
            template = templates.lookup(options.item)
            if template:
                g = r.render(assembly, assembly, template, obj_space, None,
                    shmem, kept_symbols, fill_frames, imported=read, options=options)
                save(options.item, g)
                done(g)
        except TemplateError as inst:
            die(['While rendering %s: %s' % (options.item, line) for line in inst.args])

    if options.item in ('capdl', 'label-mapping') and options.data_structure_cache_dir is not None:
        # It's possible that data structures required to instantiate the capdl spec
        # were saved during a previous invocation of this script in the current build.
        cache_path = os.path.realpath(options.data_structure_cache_dir)
        pickle_path = os.path.join(cache_path, CAPDL_STATE_PICKLE)

        if os.path.isfile(pickle_path):
            with open(pickle_path, 'rb') as pickle_file:
                # Found a cached version of the necessary data structures
                obj_space, shmem, cspaces, pds, kept_symbols, fill_frames = pickle.load(pickle_file)
                apply_capdl_filters()
                instantiate_misc_template()

                # If a template wasn't instantiated, something went wrong, and we can't recover
                raise CAmkESError("No template instantiated on capdl generation fastpath")

    # We're now ready to instantiate the template the user requested, but there
    # are a few wrinkles in the process. Namely,
    #  1. Template instantiation needs to be done in a deterministic order. The
    #     runner is invoked multiple times and template code needs to be
    #     allocated identical cap slots in each run.
    #  2. Components and connections need to be instantiated before any other
    #     templates, regardless of whether they are the ones we are after. Some
    #     other templates, such as the Makefile depend on the obj_space and
    #     cspaces.
    #  3. All actual code templates, up to the template that was requested,
    #     need to be instantiated. This is related to (1) in that the cap slots
    #     allocated are dependent on what allocations have been done prior to a
    #     given allocation call.

    # Instantiate the per-component source and header files.
    for i in assembly.composition.instances:
        # Don't generate any code for hardware components.
        if i.type.hardware:
            continue

        if i.address_space not in cspaces:
            p = Perspective(phase=RUNNER, instance=i.name,
                group=i.address_space)
            cnode = obj_space.alloc(seL4_CapTableObject,
                name=p['cnode'], label=i.address_space)
            cspaces[i.address_space] = CSpaceAllocator(cnode)
            pd = obj_space.alloc(lookup_architecture(options.architecture).vspace().object, name=p['pd'],
                label=i.address_space)
            pds[i.address_space] = pd

        for t in ('%s/source' % i.name, '%s/header' % i.name,
                '%s/linker' % i.name):
            try:
                template = templates.lookup(t, i)
                g = ''
                if template:
                    g = r.render(i, assembly, template, obj_space, cspaces[i.address_space],
                        shmem, kept_symbols, fill_frames, options=options, my_pd=pds[i.address_space])
                save(t, g)
                if options.item == t:
                    if not template:
                        log.warning('Warning: no template for %s' % options.item)
                    done(g)
            except TemplateError as inst:
                die(['While rendering %s: %s' % (i.name, line) for line in inst.args])

    # Instantiate the per-connection files.
    for c in assembly.composition.connections:

        for t in (('%s/from/source' % c.name, c.from_ends),
                  ('%s/from/header' % c.name, c.from_ends),
                  ('%s/to/source' % c.name, c.to_ends),
                  ('%s/to/header' % c.name, c.to_ends)):

            template = templates.lookup(t[0], c)

            if template is not None:
                for id, e in enumerate(t[1]):
                    item = '%s/%d' % (t[0], id)
                    g = ''
                    try:
                        g = r.render(e, assembly, template, obj_space,
                            cspaces[e.instance.address_space], shmem, kept_symbols, fill_frames,
                            options=options, my_pd=pds[e.instance.address_space])
                    except TemplateError as inst:
                        die(['While rendering %s: %s' % (item, line) for line in inst.args])
                    except jinja2.exceptions.TemplateNotFound:
                        die('While rendering %s: missing template for %s' %
                            (item, c.type.name))
                    save(item, g)
                    if options.item == item:
                        if not template:
                            log.warning('Warning: no template for %s' % options.item)
                        done(g)

        # The following block handles instantiations of per-connection
        # templates that are neither a 'source' or a 'header', as handled
        # above. We assume that none of these need instantiation unless we are
        # actually currently looking for them (== options.item). That is, we
        # assume that following templates, like the CapDL spec, do not require
        # these templates to be rendered prior to themselves.
        # FIXME: This is a pretty ugly way of handling this. It would be nicer
        # for the runner to have a more general notion of per-'thing' templates
        # where the per-component templates, the per-connection template loop
        # above, and this loop could all be done in a single unified control
        # flow.
        for t in (('%s/from/' % c.name, c.from_ends),
                  ('%s/to/' % c.name, c.to_ends)):

            if not options.item.startswith(t[0]):
                # This is not the item we're looking for.
                continue

            # If we've reached here then this is the exact item we're after.
            template = templates.lookup(options.item, c)
            if template is None:
                die('no registered template for %s' % options.item)

            for e in t[1]:
                try:
                    g = r.render(e, assembly, template, obj_space,
                        cspaces[e.instance.address_space], shmem, kept_symbols, fill_frames,
                        options=options, my_pd=pds[e.instance.address_space])
                    save(options.item, g)
                    done(g)
                except TemplateError as inst:
                    die(['While rendering %s: %s' % (options.item, line) for line in inst.args])

    # Perform any per component special generation. This needs to happen last
    # as these template needs to run after all other capabilities have been
    # allocated
    for i in assembly.composition.instances:
        # Don't generate any code for hardware components.
        if i.type.hardware:
            continue
        assert i.address_space in cspaces
        SPECIAL_TEMPLATES = [('debug', 'debug'), ('simple', 'simple'), ('rump_config', 'rumprun')]
        for special in [bl for bl in SPECIAL_TEMPLATES if conf[i.name].get(bl[0])]:
            for t in ('%s/%s' % (i.name, special[1]),):
                try:
                    template = templates.lookup(t, i)
                    g = ''
                    if template:
                        g = r.render(i, assembly, template, obj_space, cspaces[i.address_space],
                            shmem, kept_symbols, fill_frames, options=options, my_pd=pds[i.address_space])
                    save(t, g)
                    if options.item == t:
                        if not template:
                            log.warning('Warning: no template for %s' % options.item)
                        done(g)
                except TemplateError as inst:
                    die(['While rendering %s: %s' % (i.name, line) for line in inst.args])

    if options.data_structure_cache_dir is not None:
        # At this point the capdl database is in the state required for applying capdl
        # filters and generating the capdl spec. In case the capdl spec isn't the current
        # target, we pickle the database here, so when the capdl spec is built, these
        # data structures don't need to be regenerated.
        cache_path = os.path.realpath(options.data_structure_cache_dir)
        pickle_path = os.path.join(cache_path, CAPDL_STATE_PICKLE)
        with open(pickle_path, 'wb') as pickle_file:
            pickle.dump((obj_space, shmem, cspaces, pds, kept_symbols, fill_frames), pickle_file)

    if options.item in ('capdl', 'label-mapping'):
        apply_capdl_filters()

    # Instantiate any other, miscellaneous template. If we've reached this
    # point, we know the user did not request a code template.
    instantiate_misc_template()

    die('No valid element matching --item %s' % options.item)

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
