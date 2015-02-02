#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Entry point for the runner (template instantiator).'''

# Excuse this horrible prelude. When running under a different interpreter we
# have an import path that doesn't include dependencies like elftools and
# Jinja. We need to juggle the import path prior to importing them. Note, this
# code has no effect when running under the standard Python interpreter.
import platform, subprocess, sys
if platform.python_implementation() != 'CPython':
    path = eval(subprocess.check_output(['python', '-c', 'import sys; print sys.path']))
    for p in path:
        if p not in sys.path:
            sys.path.append(p)

from camkes.templates import Templates, PLATFORMS
from camkes.internal.argumentparsing import parse_args
from camkes.internal.profile import get_profiler
from camkes.internal.cache import Cache
from camkes.internal.FileSet import FileSet
import camkes.internal.log as log
import camkes.internal.constants as constants
from camkes.internal.version import version
from NameMangling import Perspective, RUNNER
from Renderer import Renderer
from Filters import CAPDL_FILTERS
from Transforms import AST_TRANSFORMS
import Context

import functools, os, traceback
from copy import deepcopy

from capdl import seL4_CapTableObject, ObjectAllocator, CSpaceAllocator, \
    ELF, seL4_PageDirectoryObject

import camkes.ast as AST
import camkes.parser as parser

# Items that should never be cached as AST_keyed entries in the compilation
# cache.
NEVER_AST_CACHE = [
    'capdl', # Can't cache because it depends on ELF contents.
]

def cache_relevant_options(opts):
    '''Return a list of tuples representing the cache-relevant command line
    options. That is, the current command line options that have a relevant
    effect on code generation.'''
    # Command line options that do not influence code generation. These are
    # used to exclude options from influencing the template cache key and,
    # incorrectly, cause the cache to miss. Each of these options has one of
    # the following justifications for being in this set:
    #  1. It is already accounted for in the cache key (e.g. platform);
    #  2. It affects the AST, which is already in the cache key (e.g. cpp); or
    #  3. It has no affect on code generation (e.g. profiler).
    # We do this as an exclude list, rather than an include list so a
    # mistakenly missing entry will cause an (safe) unnecesary cache miss, as
    # opposed to an incorrect cache hit.
    CACHE_IRRELEVANT_OPTIONS = frozenset([
        'allow_forward_references',
        'cache',
        'cache_dir',
        'cpp',
        'cpp_flag',
        'elf',
        'file',
        'import_path',
        'item',
        'outfile',
        'platform',
        'ply-optimise',
        'post_render_edit',
        'profile_log',
        'profiler',
        'verbosity',
    ])
    return sorted([x for x in opts.__dict__.items() if \
        x[0] not in CACHE_IRRELEVANT_OPTIONS])

def _die(debug, s):
    log.error(str(s))
    log.debug('\n --- Python traceback ---\n%s ------------------------\n' % \
        traceback.format_exc())
    sys.exit(-1)

def main():
    options = parse_args(constants.TOOL_RUNNER)

    # Save us having to pass debugging everywhere.
    die = functools.partial(_die, options.verbosity >= 3)

    log.set_verbosity(options.verbosity)

    def done(s):
        ret = 0
        if s:
            print >>options.outfile, s
            options.outfile.close()
            if options.post_render_edit and \
                    raw_input('Edit rendered template %s [y/N]? ' % \
                    options.outfile.name) == 'y':
                editor = os.environ.get('EDITOR', 'vim')
                ret = subprocess.call([editor, options.outfile.name])
        sys.exit(ret)

    if not options.platform or options.platform in ['?', 'help'] \
            or options.platform not in PLATFORMS:
        die('Valid --platform arguments are %s' % ', '.join(PLATFORMS))

    if not options.file or len(options.file) > 1:
        die('A single input file must be provided for this operation')

    try:
        profiler = get_profiler(options.profiler, options.profile_log)
    except Exception as inst:
        die('Failed to create profiler: %s' % str(inst))

    # Construct the compilation cache if requested.
    cache = None
    if options.cache in ['on', 'readonly', 'writeonly']:
        cache = Cache(options.cache_dir)

    f = options.file[0]
    try:
        with profiler('Reading input'):
            s = f.read()
        # Try to find this output in the compilation cache if possible. This is
        # one of two places that we check in the cache. This check will 'hit'
        # if the source files representing the input spec are identical to some
        # previous execution.
        if options.cache in ['on', 'readonly']:
            with profiler('Looking for a cached version of this output'):
                key = [version(), os.path.abspath(f.name), s,
                    cache_relevant_options(options), options.platform,
                    options.item]
                value = cache.get(key)
                if value is not None and value.valid():
                    # Cache hit.
                    assert isinstance(value, FileSet), \
                        'illegally cached a value for %s that is not a FileSet' % options.item
                    log.debug('Retrieved %(platform)s.%(item)s from cache' % \
                        options.__dict__)
                    done(value.output)
        with profiler('Parsing input'):
            ast = parser.parse_to_ast(s, options.cpp, options.cpp_flag, options.ply_optimise)
            ast = compose_assemblies(ast)
            parser.assign_filenames(ast, f.name)
    except parser.CAmkESSyntaxError as e:
        e.set_column(s)
        die('%s:%s' % (f.name, str(e)))
    except Exception as inst:
        die('While parsing \'%s\': %s' % (f.name, str(inst)))

    try:
        for t in AST_TRANSFORMS:
            with profiler('Running AST transform %s' % t.__name__):
                ast = t(ast)
    except Exception as inst:
        die('While transforming AST: %s' % str(inst))

    try:
        with profiler('Resolving imports'):
            ast, imported = parser.resolve_imports(ast, \
                os.path.dirname(os.path.abspath(f.name)), options.import_path,
                options.cpp, options.cpp_flag, options.ply_optimise)
    except Exception as inst:
        die('While resolving imports of \'%s\': %s' % (f.name, str(inst)))
    with profiler('Caching original AST'):
        orig_ast = deepcopy(ast)
    with profiler('Deduping AST'):
        ast = parser.dedupe(ast)
    try:
        with profiler('Resolving references'):
            ast = parser.resolve_references(ast, False)
    except Exception as inst:
        die('While resolving references of \'%s\': %s' % (f.name, str(inst)))

    try:
        with profiler('Collapsing references'):
            parser.collapse_references(ast)
    except Exception as inst:
        die('While collapsing references of \'%s\': %s' % (f.name, str(inst)))

    ast = resolve_hierarchy(ast)

    # If we have a readable cache check if our current target is in the cache.
    # The previous check will 'miss' and this one will 'hit' when the input
    # spec is identical to some previous execution modulo a semantically
    # irrelevant element (e.g. an introduced comment). I.e. the previous check
    # matches when the input is exactly the same and this one matches when the
    # AST is unchanged.
    if options.cache in ['on', 'readonly']:
        with profiler('Looking for a cached version of this output'):
            key = [version(), orig_ast, cache_relevant_options(options),
                options.platform, options.item]
            value = cache.get(key)
            if value is not None:
                assert options.item not in NEVER_AST_CACHE, \
                    '%s, that is marked \'never cache\' is in your cache' % options.item
                log.debug('Retrieved %(platform)s.%(item)s from cache' % \
                    options.__dict__)
                done(value)

    # If we have a writable cache, allow outputs to be saved to it.
    if options.cache in ['on', 'writeonly']:
        fs = FileSet(imported)
        def save(item, value):
            # Save an input-keyed cache entry. This one is based on the
            # pre-parsed inputs to save having to derive the AST (parse the
            # input) in order to locate a cache entry in following passes.
            # This corresponds to the first cache check above.
            key = [version(), os.path.abspath(options.file[0].name), s,
                cache_relevant_options(options), options.platform,
                item]
            specialised = fs.specialise(value)
            if item == 'capdl':
                specialised.extend(options.elf or [])
            cache[key] = specialised
            if item not in NEVER_AST_CACHE:
                # Save an AST-keyed cache entry. This corresponds to the second
                # cache check above.
                cache[[version(), orig_ast, cache_relevant_options(options),
                    options.platform, item]] = value
    else:
        def save(item, value):
            pass

    # All references in the AST need to be resolved for us to continue.
    unresolved = reduce(lambda a, x: a.union(x),
        map(lambda x: x.unresolved(), ast), set())
    if unresolved:
        die('Unresolved references in input specification:\n %s' % \
            '\n '.join(map(lambda x: '%(filename)s:%(lineno)s:\'%(name)s\' of type %(type)s' % {
                'filename':x.filename or '<unnamed file>',
                'lineno':x.lineno,
                'name':x._symbol,
                'type':x._type.__name__,
            }, unresolved)))

    # Locate the assembly
    assembly = [x for x in ast if isinstance(x, AST.Assembly)]
    if len(assembly) > 1:
        die('Multiple assemblies found')
    elif len(assembly) == 1:
        assembly = assembly[0]
    else:
        die('No assembly found')

    obj_space = ObjectAllocator()
    cspaces = {}
    pds = {}
    conf = assembly.configuration
    shmem = {}

    # We need to create a phony instance and connection to cope with cases
    # where the user has not defined any instances or connections (this would
    # be an arguably useless system, but we should still support it). We append
    # these to the template's view of the system below to ensure we always get
    # a usable template dictionary. Note that this doesn't cause any problems
    # because the phony items are named '' and thus unaddressable in ADL.
    dummy_instance = AST.Instance(AST.Reference('', AST.Instance), '')
    dummy_connection = AST.Connection(AST.Reference('', AST.Connector), '', \
        AST.Reference('', AST.Instance), AST.Reference('', AST.Interface), \
        AST.Reference('', AST.Instance), AST.Reference('', AST.Interface))

    templates = Templates(options.platform,
        instance=map(lambda x: x.name, assembly.composition.instances + \
            [dummy_instance]), \
        connection=map(lambda x: x.name, assembly.composition.connections + \
            [dummy_connection]))
    if options.templates:
        templates.add_root(options.templates)
    r = Renderer(templates.get_roots(), options)

    # The user may have provided their own connector definitions (with
    # associated) templates, in which case they won't be in the built-in lookup
    # dictionary. Let's add them now. Note, definitions here that conflict with
    # existing lookup entries will overwrite the existing entries.
    for c in [x for x in ast if isinstance(x, AST.Connector)]:
        if c.from_template:
            templates.add(c.name, 'from.source', c.from_template)
        if c.to_template:
            templates.add(c.name, 'to.source', c.to_template)

    # The user can pass settings on the command line as '--set=foo' or
    # '--set=foo=bar', which makes the variable 'foo' available inside the
    # template context. Using the first syntax it is set to 'True', while in
    # the second it is set to the string 'bar'. We need to set this up in a bit
    # of a convoluted way to guard against the user setting variables that
    # inadvertently override named parameters to `render` and/or `new_context`.
    cmdln_opts = {}
    for s in options.set:
        key, value = (s.split('=', 1) + [True])[:2]
        cmdln_opts[key] = value
    conflict = set(cmdln_opts).intersection( \
        set(r.render.func_code.co_varnames).union( \
            set(Context.new_context.func_code.co_varnames))) #pylint: disable=E1101
    if conflict:
        die('Attempt to set restricted option(s) %s' % ', '.join(conflict))

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
    for id, i in enumerate(assembly.composition.instances):
        # Don't generate any code for hardware components.
        if i.type.hardware:
            continue

        if i.address_space not in cspaces:
            cnode = obj_space.alloc(seL4_CapTableObject,
                name='cnode_%s' % i.address_space, label=i.address_space)
            cspaces[i.address_space] = CSpaceAllocator(cnode)
            p = Perspective(phase=RUNNER, instance=i.name,
                group=i.address_space)
            pd = obj_space.alloc(seL4_PageDirectoryObject, name=p['pd'],
                label=i.address_space)
            pds[i.address_space] = pd

        for t in ['%s.source' % i.name, '%s.header' % i.name]:
            try:
                template = templates.lookup(t, i)
                g = ''
                if template:
                    with profiler('Rendering %s' % t):
                        g = r.render(i, conf, template, obj_space, cspaces[i.address_space], \
                            shmem, options=options, id=id, my_pd=pds[i.address_space], \
                            **cmdln_opts)
                save(t, g)
                if options.item == t:
                    if not template:
                        log.warning('Warning: no template for %s' % options.item)
                    done(g)
            except Exception as inst:
                die('While rendering %s: %s' % (i.name, str(inst)))

    # Instantiate the per-connection files.
    conn_dict = {}
    for id, c in enumerate(assembly.composition.connections):
        tmp_name = c.name
        key_from = (c.from_instance.name + '_' + c.from_interface.name) in conn_dict
        key_to = (c.to_instance.name + '_' + c.to_interface.name) in conn_dict
        if not key_from and not key_to:
            # We need a new connection name
            conn_name = 'conn' + str(id)
            c.name = conn_name
            conn_dict[c.from_instance.name + '_' + c.from_interface.name] = conn_name
            conn_dict[c.to_instance.name + '_' + c.to_interface.name] = conn_name
        elif not key_to:
            conn_name = conn_dict[c.from_instance.name + '_' + c.from_interface.name]
            c.name = conn_name
            conn_dict[c.to_instance.name + '_' + c.to_interface.name] = conn_name
        elif not key_from:
            conn_name = conn_dict[c.to_instance.name + '_' + c.to_interface.name]
            c.name = conn_name
            conn_dict[c.from_instance.name + '_' + c.from_interface.name] = conn_name
        else:
            continue

        for t in [('%s.from.source' % tmp_name, c.from_instance.address_space),
                  ('%s.from.header' % tmp_name, c.from_instance.address_space),
                  ('%s.to.source' % tmp_name, c.to_instance.address_space),
                  ('%s.to.header' % tmp_name, c.to_instance.address_space)]:
            try:
                template = templates.lookup(t[0], c)
                g = ''
                if template:
                    with profiler('Rendering %s' % t[0]):
                        g = r.render(c, conf, template, obj_space, cspaces[t[1]], \
                            shmem, options=options, id=id, my_pd=pds[t[1]], \
                            **cmdln_opts)
                save(t[0], g)
                if options.item == t[0]:
                    if not template:
                        log.warning('Warning: no template for %s' % options.item)
                    done(g)
            except Exception as inst:
                die('While rendering %s: %s' % (t[0], str(inst)))
        c.name = tmp_name

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
        for t in [('%s.from.' % c.name, c.from_instance.address_space),
                  ('%s.to.' % c.name, c.to_instance.address_space)]:
            if not options.item.startswith(t[0]):
                # This is not the item we're looking for.
                continue
            try:
                # If we've reached here then this is the exact item we're
                # after.
                template = templates.lookup(options.item, c)
                if template is None:
                    raise Exception('no registered template for %s' % options.item)
                with profiler('Rendering %s' % options.item):
                    g = r.render(c, conf, template, obj_space, cspaces[t[1]], \
                        shmem, options=options, id=id, my_pd=pds[t[1]], \
                        **cmdln_opts)
                save(options.item, g)
                done(g)
            except Exception as inst:
                die('While rendering %s: %s' % (options.item, str(inst)))

    # Perform any per component simple generation. This needs to happen last
    # as this template needs to run after all other capabilities have been
    # alloacted
    for id, i in enumerate(assembly.composition.instances):
        # Don't generate any code for hardware components.
        if i.type.hardware:
            continue
        assert i.address_space in cspaces
        if conf and conf.settings and [x for x in conf.settings if \
                x.instance == i.name and x.attribute == 'simple' and x.value]:
            for t in ['%s.simple' % i.name]:
                try:
                    template = templates.lookup(t, i)
                    g = ''
                    if template:
                        with profiler('Rendering %s' % t):
                            g = r.render(i, conf, template, obj_space, cspaces[i.address_space], \
                                shmem, options=options, id=id, my_pd=pds[i.address_space], 
                                **cmdln_opts)
                    save(t, g)
                    if options.item == t:
                        if not template:
                            log.warning('Warning: no template for %s' % options.item)
                        done(g)
                except Exception as inst:
                    die('While rendering %s: %s' % (i.name, str(inst)))

    # Derive a set of usable ELF objects from the filenames we were passed.
    elfs = {}
    arch = None
    for e in options.elf or []:
        try:
            name = os.path.basename(e)
            if name in elfs:
                raise Exception('duplicate ELF files of name \'%s\' encountered' % name)
            elf = ELF(e, name)
            if not arch:
                # The spec's arch will have defaulted to ARM, but we want it to
                # be the same as whatever ELF format we're parsing.
                arch = elf.get_arch()
                if arch == 'ARM':
                    obj_space.spec.arch = 'arm11'
                elif arch == 'x86':
                    obj_space.spec.arch = 'ia32'
                else:
                    raise NotImplementedError
            else:
                # All ELF files we're parsing should be the same format.
                if arch != elf.get_arch():
                    raise Exception('ELF files are not all the same architecture')
            # Pass 'False' to avoid inferring a TCB as we've already created
            # our own.
            p = Perspective(phase=RUNNER, elf_name=name)
            group = p['group']
            with profiler('Deriving CapDL spec from %s' % e):
                elf_spec = elf.get_spec(infer_tcb=False, infer_asid=False,
                    pd=pds[group])
                obj_space.merge(elf_spec, label=group)
            elfs[name] = (e, elf)
        except Exception as inst:
            die('While opening \'%s\': %s' % (e, str(inst)))

    if options.item in ['capdl', 'label-mapping']:
        # It's only relevant to run these filters if the final target is CapDL.
        # Note, this will no longer be true if we add any other templates that
        # depend on a fully formed CapDL spec. Guarding this loop with an if
        # is just an optimisation and the conditional can be removed if
        # desired.
        for f in CAPDL_FILTERS:
            try:
                with profiler('Running CapDL filter %s' % f.__name__):
                    f(ast, obj_space, cspaces, elfs,
                        profiler, options)
            except Exception as inst:
                die('While forming CapDL spec: %s' % str(inst))

    # Instantiate any other, miscellaneous template. If we've reached this
    # point, we know the user did not request a code template.
    try:
        template = templates.lookup(options.item)
        g = ''
        if template:
            with profiler('Rendering %s' % options.item):
                g = r.render(assembly, conf, template, obj_space, None, \
                    shmem, imported=imported, options=options, **cmdln_opts)
            save(options.item, g)
            done(g)
    except Exception as inst:
        die('While rendering %s: %s' % (options.item, str(inst)))

    die('No valid element matching --item %s' % options.item)

def compose_assemblies(ast):
    # parts of assembly
    instances = []
    connections = []
    groups = []
    settings = []

    filename = None
    lineno = -1

    # collect pieces from all assemblies
    for a in filter(lambda x: isinstance(x, AST.Assembly), ast):

        if filename == None:
            filename = a.filename

        if lineno == -1:
            lineno = a.lineno

        for i in a.composition.instances:
            instances.append(i)
        for c in a.composition.connections:
            connections.append(c)
        for g in a.composition.groups:
            groups.append(g)

        if a.configuration is not None:
            for s in a.configuration.settings:
                settings.append(s)

    # create an assembly composed from all the pieces
    composite_assembly = AST.Assembly(None,
                            AST.Composition(None, instances, connections, groups),
                            AST.Configuration(None, settings),
                            filename, lineno
                        )
 
    # remove all the assemblies from ast
    ast = [x for x in ast if not isinstance(x, AST.Assembly)]

    # add the new composite assembly
    ast.append(composite_assembly)

    return ast

def resolve_hierarchy(ast):
    # find the assembly
    assembly = [x for x in ast if isinstance(x, AST.Assembly)]
    assert len(assembly) == 1
    assembly = assembly[0]
    
    # modify the ast to resolve the hierarchy
    assembly = resolve_assembly_hierarchy(assembly)
    
    # remove the assembly from the ast
    ast[:] = [x for x in ast if not isinstance(x, AST.Assembly)]

    # replace it with the new one
    ast.append(assembly)

    # remove all the component interfaces with virtual usage
    for c in [x for x in ast if isinstance(x, AST.Component)]:
        remove_virtual_interfaces(c)

    return ast

def merge_assembly(dest, source, instance):
    '''Copies all the assembly elements from source into dest, where
       instance is a composite component instance in dest, whose component's
       assembly is source. Any connectors in dest which connect an exported
       interface of the given instance are changed to connect to the
       actual component instance that implements that interface'''
       
    # copy instances, groups and configuration settings
    dest.composition.instances.extend(source.composition.instances)
    dest.composition.groups.extend(source.composition.groups)
    dest.configuration.settings.extend(source.configuration.settings)

    # create dict mapping exported interface name -> source connector
    exports = {}
    for c in source.composition.connections:
        internal = True

        # special instance name for the exported side of a connection
        if c.from_instance.name == '__virtual__':
            internal = False

            if c.from_interface.name in exports:
                raise Exception("Multiple declaration of interface %s in component %s." \
                                    % (c.from_interface.name, source.name))

            exports[c.from_interface.name] = c

        if c.to_instance.name == '__virtual__':
            internal = False

            if c.to_interface.name in exports:
                raise Exception("Multiple declaration of interface %s in component %s." \
                                    % (c.to_interface.name, source.name))

            exports[c.to_interface.name] = c

        # all non export connectors are copied straight to dest
        if internal:
            dest.composition.connections.append(c)

    # find all the connections in dest with the given instance on one side
    # and the interface of the given instance is exported by in the source 
    # assembly, replacing the instance and interface of that side of the
    # connection with the corresponding one from the source
    for c in dest.composition.connections:
        if c.from_instance == instance and c.from_interface.name in exports:
            sc = exports[c.from_interface.name]
            c.from_instance = sc.from_instance
            c.from_interface = sc.from_interface
        if c.to_instance == instance and c.to_interface.name in exports:
            sc = exports[c.to_interface.name]
            c.to_instance = sc.to_instance
            c.to_interface = sc.to_interface

def prefix_children(prefix, assembly):
    '''prepends a given prefix to all the elements of the assembly'''

    for i in assembly.composition.instances:
        i.name = '%s_%s' % (prefix, i.name)
        i.address_space = i.name
    for c in assembly.composition.connections:
        c.name = '%s_%s' % (prefix, c.name)
    for g in assembly.composition.groups:
        g.name = '%s_%s' % (prefix, g.name)
    for s in assembly.configuration.settings:
        s.instance = '%s_%s' % (prefix, s.instance)

def resolve_assembly_hierarchy(original):
    '''Given something that has a composition and optionally a configuration
       (ie. an assembly or composite original), this returns a new Assembly
       containing instances and connections in which any hierarchy below the
       given original are resolved.'''

    # create empty assembly to populate
    resolved = AST.Assembly(composition = AST.Composition(), configuration = AST.Configuration())

    # non-composite components don't have any instances or connections
    if original.composition is None:
        return resolved

    # copy the instances, connections, groups and configuration
    resolved.composition.instances.extend(original.composition.instances)
    resolved.composition.connections.extend(original.composition.connections)
    resolved.composition.groups.extend(original.composition.groups)

    if original.configuration is not None:
        resolved.configuration.settings.extend(original.configuration.settings)
    
    # recursively resolve hierarchy of instances
    for i in original.composition.instances:

        # if i is an instance of a compound component
        if i.type.composition is not None:
            
            # get the assembly from that component
            # deepcopying prevents modifying the original component's composition's
            # children, which must be preserved for future instantiation of the
            # component
            resolved_instance = resolve_assembly_hierarchy(deepcopy(i.type))
            
            # rename assembly elements to indicate them as part of a sub assembly
            prefix_children(i.name, resolved_instance)
            
            # merge it into the current assembly
            merge_assembly(resolved, resolved_instance, i)

    return resolved

def remove_virtual_interfaces(component):
    '''modifies the component (not an instance), removing all interfaces
       which aren't implemented by that component (ie. implemented by a
       sub component) so no code is generated for those interfaces'''

    if component.composition is not None:
        unimplemented_interfaces = []
        for conn in component.composition.connections:
            if conn.from_instance.name == '__virtual__':
                unimplemented_interfaces.append(conn.from_interface)
            if conn.to_instance.name == '__virtual__':
                unimplemented_interfaces.append(conn.to_interface)

        for i in unimplemented_interfaces:
            if isinstance(i, AST.Provides):
                component.provides.remove(i)
            elif isinstance(i, AST.Uses):
                component.uses.remove(i)
            elif isinstance(i, AST.Emits):
                component.emits.remove(i)
            elif isinstance(i, AST.Consumes):
                component.consumes.remove(i)
            elif isinstance(i, AST.Dataport):
                component.dataport.remove(i)
            elif isinstance(i, AST.Mutex):
                component.mutexes.remove(i)
            elif isinstance(i, AST.Semaphore):
                component.semaphores.remove(i)


if __name__ == '__main__':
    sys.exit(main())
