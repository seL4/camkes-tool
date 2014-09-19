#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Filters to be applied to generated CapDL.'''

import os, re, subprocess
import camkes.ast as AST
from capdl import Cap, CNode, TCB, page_table_index, page_index
from camkes.internal.memoization import memoized
from NameMangling import Perspective

PAGE_SIZE = 4096 # bytes
IPC_BUFFER_SIZE = 512 # bytes

def find_assembly(ast):
    assemblies = filter(lambda x: isinstance(x, AST.Assembly), ast)
    assert len(assemblies) == 1 # Our parent should have ensured this.
    return assemblies[0]

# PERF/HACK: This function is memoized and optionally calls out to objdump
# because it becomes a performance bottleneck in large systems. Note that the
# second branch here is much more reliable and you should use it when possible.
objdump_output = {}
@memoized
def get_symbol(elf, symbol):
    if os.environ.get('CONFIG_CAMKES_USE_EXTERNAL_OBJDUMP', '') == 'y':
        global objdump_output
        stdout = objdump_output.get(elf[0])
        if stdout is None:
            # We haven't run objdump on this output yet. Need to do it now.
            toolprefix = os.environ.get('TOOLPREFIX', '')
            # Construct the bash invocation we want
            argument = "%sobjdump --syms %s | grep -E '^[0-9a-fA-F]{8}' | sed -r 's/^([0-9a-fA-F]{8})[ \\t].*[ \\t]([0-9a-fA-F]{8})[ \\t]+(.*)/\\3 \\1 \\2/'" % (toolprefix, elf[0])
            stdout = subprocess.check_output(['sh','-c',argument])
            # Cache the result for future symbol lookups.
            objdump_output[elf[0]] = stdout
        sym_index = stdout.find('\n%s ' % symbol);
        if sym_index == -1:
            return None, None
        vaddr_index = sym_index + len(symbol) + 2;
        size_index = vaddr_index + 9;
        return int(stdout[vaddr_index:vaddr_index+8], 16), \
            int(stdout[size_index:size_index+8], 16)
    else:
        return elf[1].get_symbol_vaddr(symbol), elf[1].get_symbol_size(symbol)

def get_symbol_vaddr(elf, symbol):
    return get_symbol(elf, symbol)[0]
def get_symbol_size(elf, symbol):
    return get_symbol(elf, symbol)[1]
def get_entry_point(elf):
    return elf[1].get_entry_point()
def get_elf_arch(elf):
    return elf[1].get_arch()

def set_tcb_info(ast, obj_space, cspaces, elfs, *_):
    '''Set relevant extra info for TCB objects.'''

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, cap in cnode.slots.items():
            # We only care about the TCBs.
            if cap is None:
                continue
            tcb = cap.referent
            if not isinstance(tcb, TCB):
                continue

            perspective = Perspective(group=group, tcb=tcb.name)

            elf_name = perspective['elf_name']

            elf = elfs.get(elf_name)

            if elf is None:
                # We were not passed an ELF file for this CSpace. This will be
                # true in the first pass of the runner where no ELFs are passed.
                continue

            tcb.elf = elf_name
            tcb.ip = get_entry_point(elf)

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
                2 * PAGE_SIZE - IPC_BUFFER_SIZE

            # Each TCB needs to be passed its 'thread_id' that is the value
            # it branches on in main(). This corresponds to the slot index
            # to a cap to it in the component's CNode.
            tcb.init.append(index)

            # The group's entry point expects to be passed a function pointer
            # as the second argument that is the instance's entry point.
            component_entry = perspective['entry_symbol']
            vaddr = get_symbol_vaddr(elf, component_entry)
            if vaddr is None:
                raise Exception('Entry point, %s, of %s not found' %
                    (component_entry, tcb.name))
            tcb.init.append(vaddr)

            # The group's entry point expects to be passed a function pointer
            # as the third argument that is a function that will perform
            # early tls setup
            tls_setup = perspective['tls_symbol']
            vaddr = get_symbol_vaddr(elf, tls_setup)
            if vaddr is None:
                raise Exception('TLS symbol, %s, of %s not found' % (tls_setup, tcb.name))
            tcb.init.append(vaddr)

def set_tcb_caps(ast, obj_space, cspaces, elfs, *_):
    for group, space in cspaces.items():
        cnode = space.cnode
        for index, cap in cnode.slots.items():

            if cap is None:
                continue
            tcb = cap.referent
            if not isinstance(tcb, TCB):
                continue

            perspective = Perspective(tcb=tcb.name, group=group)

            # Finalise the CNode so that we know what its absolute size will
            # be. Note that we are assuming no further caps will be added to
            # the CNode after this point.
            cnode.finalise_size()

            cspace = Cap(cnode)
            cspace.set_guard_size(32 - cnode.size_bits)
            tcb['cspace'] = cspace

            elf_name = perspective['elf_name']

            pd = None
            pd_name = perspective['pd']
            pds = filter(lambda x: x.name == pd_name, obj_space.spec.objs)
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

            elf = elfs.get(elf_name)

            if pd and elf:

                ipc_symbol = perspective['ipc_buffer_symbol']

                # Find the IPC buffer's virtual address.
                assert get_symbol_size(elf, ipc_symbol) == PAGE_SIZE * 3
                ipc_vaddr = get_symbol_vaddr(elf, ipc_symbol) + PAGE_SIZE

                # Relate this virtual address to a PT.
                pt_index = page_table_index(get_elf_arch(elf), ipc_vaddr)
                if pt_index not in pd:
                    raise Exception('IPC buffer of TCB %s in group %s does ' \
                        'not appear to be backed by a frame' % (tcb.name, group))
                pt = pd[pt_index].referent

                # Continue on to infer the physical frame.
                p_index = page_index(get_elf_arch(elf), ipc_vaddr)
                if p_index not in pt:
                    raise Exception('IPC buffer of TCB %s in group %s does ' \
                        'not appear to be backed by a frame' % (tcb.name, group))
                frame = pt[p_index].referent

                tcb['ipc_buffer_slot'] = Cap(frame, True, True, True) # RWG

            # Currently no fault EP (fault_ep_slot).

def collapse_shared_frames(ast, obj_space, cspaces, elfs, *_):
    """Find regions in virtual address spaces that are intended to be backed by
    shared frames and adjust the capability distribution to reflect this."""

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    assembly = find_assembly(ast)

    settings = \
        assembly.configuration.settings if assembly.configuration is not None \
        else []

    # We want to track the frame objects backing shared regions with a dict
    # keyed on the name of the connection linking the regions.
    shared_frames = {}

    for i in assembly.composition.instances:
        if i.type.hardware:
            continue

        perspective = Perspective(instance=i.name, group=i.address_space)

        elf_name = perspective['elf_name']
        assert elf_name in elfs
        elf = elfs[elf_name]

        # Find this instance's page directory.
        pd_name = perspective['pd']
        pds = filter(lambda x: x.name == pd_name, obj_space.spec.objs)
        assert len(pds) == 1
        pd, = pds

        for d in i.type.dataports:

            # Find the connection that associates this dataport with another.
            connections = filter(lambda x: \
                (x.from_instance == i and x.from_interface == d) or \
                (x.to_instance == i and x.to_interface == d), \
                assembly.composition.connections)
            if len(connections) == 0:
                # This dataport is unconnected.
                continue
            #assert len(connections) == 1
            conn_name = connections[0].name

            if connections[0].from_instance == i and \
                    connections[0].from_interface == d:
                direction = 'from'
            else:
                assert connections[0].to_instance == i
                assert connections[0].to_interface == d
                direction = 'to'

            # Reverse the logic in the Makefile template.
            p = Perspective(instance=i.name, dataport=d.name)
            sym = p['dataport_symbol']

            vaddr = get_symbol_vaddr(elf, sym)
            assert vaddr is not None, 'failed to find dataport symbol \'%s\'' \
                ' in ELF %s' % (sym, elf_name)
            assert vaddr != 0
            sz = get_symbol_size(elf, sym)
            assert sz != 0

            # Infer the page table that backs this vaddr.
            pt_index = page_table_index(get_elf_arch(elf), vaddr)
            assert pt_index in pd
            pt = pd[pt_index].referent

            # Infer the starting page index of this vaddr.
            p_index = page_index(get_elf_arch(elf), vaddr)

            # TODO: If the following assertion fails it means that the shared
            # region crosses a PT boundary (i.e. it is backed by more than one
            # PT). In theory we could support this with a bit more cleverness
            # here.
            assert page_table_index(get_elf_arch(elf), vaddr + sz - 1) == pt_index

            # Determine the rights this mapping should have. We use these to
            # recreate the mapping below. Technically we may not need to
            # recreate this mapping if it's already correct, but do it anyway
            # for simplicity.
            # FIXME: stop hard coding this name mangling.
            rights_setting = filter(lambda x: x.instance == conn_name and \
                x.attribute == '%s_access' % direction, settings)
            if len(rights_setting) == 1 and \
                    re.match(r'^"R?W?(G|X)?"$', rights_setting[0].value):
                read = 'R' in rights_setting[0].value
                write = 'W' in rights_setting[0].value
                execute = 'X' in rights_setting[0].value or \
                    'G' in rights_setting[0].value
            else:
                # default
                read = True
                write = True
                execute = False

            # Check if the dataport is connected *TO* a hardware component.
            if connections[0].to_instance.type.hardware and \
                    assembly.configuration is not None:
                p = Perspective(to_interface=connections[0].to_interface.name)
                hardware_attribute = p['hardware_attribute']
                configurations = filter(lambda x: \
                    (x.instance == connections[0].to_instance.name and \
                     x.attribute == hardware_attribute), \
                    assembly.configuration.settings)
                assert len(configurations) == 1
                paddr, size = configurations[0].value.strip('"').split(':')
                # Round up the MMIO size to PAGE_SIZE
                size = int(size, 16)
                for idx in range(0, (size + PAGE_SIZE - 1) / PAGE_SIZE):
                    frame_obj = pt[p_index + idx].referent
                    frame_obj.paddr = int(paddr, 16) + PAGE_SIZE * idx
                    cap = Cap(frame_obj, read, write, execute)
                    cap.set_cached(False)
                    pt.slots[p_index + idx] = cap
                    obj_space.relabel(conn_name, frame_obj)

                continue

            shm_keys = []
            for c in connections:
                shm_keys.append('%s_%s' % (c.from_instance.name, c.from_interface.name))
                shm_keys.append('%s_%s' % (c.to_instance.name, c.to_interface.name))

            mapped = filter(lambda x: x in shared_frames, shm_keys)
            if mapped:
                # We've already encountered the other side of tnhis dataport.

                # The region had better be the same size in all address spaces.
                for key in mapped:
                    assert len(shared_frames[key]) == sz / PAGE_SIZE

            # This is the first side of this dataport.

            # Save all the frames backing this region.
            for key in shm_keys:
                if mapped:
                    shared_frames[key] = shared_frames[mapped[0]]
                else:
                    shared_frames[key] = \
                        map(lambda x: pt[p_index + x].referent, \
                        range(0, sz / PAGE_SIZE))

            # Overwrite the caps backing this region with caps to the shared
            # frames. Again, note we may not need to do this, but doing it
            # unconditionally is simpler.
            for j in range(0, sz / PAGE_SIZE):
                f = shared_frames[shm_keys[0]][j]
                pt.slots[p_index + j] = Cap(f, read, write, execute)
                obj_space.relabel(conn_name, f)

def guard_cnode_caps(ast, obj_space, cspaces, *_):
    '''If the templates have allocated any caps to CNodes, they will not have
    the correct guards. This is due to the CNodes' sizes being automatically
    calculated (during set_tcb_caps above). Correct them here.'''

    for space in cspaces.values():
        for cap in space.cnode.slots.values():
            if cap is not None and isinstance(cap.referent, CNode):
                cap.set_guard_size(32 - cap.referent.size_bits)

def guard_pages(ast, obj_space, cspaces, elfs, *_):
    '''Introduce a guard page around each stack and IPC buffer. Note that the
    templates should have ensured a three page region for each stack in order to
    enable this.'''

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, cap in cnode.slots.items():

            if cap is None:
                continue
            tcb = cap.referent
            if not isinstance(tcb, TCB):
                continue

            perspective = Perspective(group=group, tcb=tcb.name)

            if perspective['pool']:
                # This TCB is part of the (cap allocator's) TCB pool.
                continue

            elf_name = perspective['elf_name']

            # Find the page directory.
            pd = None
            pd_name = perspective['pd']
            pds = filter(lambda x: x.name == pd_name, obj_space.spec.objs)
            if len(pds) > 1:
                raise Exception('Multiple PDs found for group %s' % group)
            elif len(pds) == 1:
                pd, = pds
                tcb['vspace'] = Cap(pd)
            # If no PD was found we were probably just not passed any ELF files
            # in this pass.

            elf = elfs.get(elf_name)

            if pd and elf:

                ipc_symbol = perspective['ipc_buffer_symbol']

                # Find the IPC buffer's preceding guard page's virtual address.
                assert get_symbol_size(elf, ipc_symbol) == PAGE_SIZE * 3
                pre_guard = get_symbol_vaddr(elf, ipc_symbol)

                # Relate this virtual address to a PT.
                pt_index = page_table_index(get_elf_arch(elf), pre_guard)
                if pt_index not in pd:
                    raise Exception('IPC buffer region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                # Continue on to infer the page.
                p_index = page_index(get_elf_arch(elf), pre_guard)
                if p_index not in pt:
                    raise Exception('IPC buffer region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                # Delete the page.
                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.spec.objs.remove(frame)

                # Now do the same for the following guard page. We do this
                # calculation separately just in case the region crosses a PT
                # boundary and the two guard pages are in separate PTs.

                post_guard = pre_guard + 2 * PAGE_SIZE

                pt_index = page_table_index(get_elf_arch(elf), post_guard)
                if pt_index not in pd:
                    raise Exception('IPC buffer region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), post_guard)
                if p_index not in pt:
                    raise Exception('IPC buffer region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.spec.objs.remove(frame)

                # Now we do the same thing for the preceding guard page of the
                # thread's stack...

                stack_symbol = perspective['stack_symbol']

                pre_guard = get_symbol_vaddr(elf, stack_symbol)

                pt_index = page_table_index(get_elf_arch(elf), pre_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), pre_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.spec.objs.remove(frame)

                # ...and the following guard page.

                stack_region_size = get_symbol_size(elf, stack_symbol)
                assert stack_region_size % PAGE_SIZE == 0, \
                    'stack region is not page-aligned'
                assert stack_region_size >= 3 * PAGE_SIZE, \
                    'stack region has no room for guard pages'
                post_guard = pre_guard + stack_region_size - PAGE_SIZE

                pt_index = page_table_index(get_elf_arch(elf), post_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), post_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.spec.objs.remove(frame)

def tcb_default_priorities(ast, obj_space, cspaces, elfs, profiler, options):
    '''Set up default thread priorities. Note this filter needs to operate
    *before* tcb_priorities.'''

    for t in filter(lambda x: isinstance(x, TCB), obj_space):
        t.prio = options.default_priority

def tcb_priorities(ast, obj_space, cspaces, *_):
    ''' Override a TCB's default priority if the user has specified this in an
    attribute.'''

    assembly = find_assembly(ast)

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no priorities were set.
        return

    settings = assembly.configuration.settings

    for group, space in cspaces.items():
        cnode = space.cnode
        for cap in cnode.slots.values():

            if cap is None:
                continue
            tcb = cap.referent
            if not isinstance(tcb, TCB):
                continue

            perspective = Perspective(group=group, tcb=tcb.name)

            # Find the priority if it was set.
            prio_attribute = perspective['priority_attribute']
            name = perspective['instance']
            prios = filter(lambda x: \
                x.instance == name and x.attribute == prio_attribute,
                settings)
            if len(prios) != 1:
                continue
            prio = prios[0].value

            tcb.prio = prio

def tcb_domains(ast, obj_space, cspaces, *_):
    '''Set the domain of a TCB if the user has specified this in an
    attribute.'''

    assembly = find_assembly(ast)

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no domains were set.
        return

    settings = assembly.configuration.settings

    for group, space in cspaces.items():
        cnode = space.cnode
        for tcb in filter(lambda x: isinstance(x, TCB),
                [x.referent for x in filter(None, cnode.slots.values())]):

            perspective = Perspective(group=group, tcb=tcb.name)

            # Find the domain if it was set.
            dom_attribute = perspective['domain_attribute']
            name = perspective['instance']
            doms = filter(lambda x: \
                x.instance == name and x.attribute == dom_attribute,
                settings)
            if len(doms) != 1:
                continue
            dom = doms[0].value

            tcb.domain = dom

def remove_tcb_caps(ast, obj_space, cspaces, elfs, profiler, options):
    '''Remove all TCB caps in the system if requested by the user.'''
    if not options.fprovide_tcb_caps:
        for space in cspaces.values():
            for slot in space.cnode.slots.keys():
                if isinstance(space.cnode[slot].referent, TCB):
                    del space.cnode[slot]

CAPDL_FILTERS = [
    set_tcb_info,
    set_tcb_caps,
    collapse_shared_frames,
    guard_cnode_caps,
    guard_pages,
    tcb_default_priorities,
    tcb_priorities,
    tcb_domains,
    remove_tcb_caps,
]
