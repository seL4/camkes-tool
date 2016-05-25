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
from capdl import Cap, CNode, TCB, SC, page_table_index, page_index, \
                  Frame, seL4_ARM_SectionObject, seL4_IA32_4M
from camkes.internal.memoization import memoized
from NameMangling import Perspective

PAGE_SIZE = 4096 # bytes
IPC_BUFFER_SIZE = 512 # bytes

def find_assembly(ast):
    assemblies = [x for x in ast if isinstance(x, AST.Assembly)]
    assert len(assemblies) == 1 # Our parent should have ensured this.
    return assemblies[0]

# PERF/HACK: This function is memoized and optionally calls out to objdump
# because it becomes a performance bottleneck in large systems. Note that the
# second branch here is much more reliable and you should use it when possible.
objdump_output = {}
@memoized
def get_symbol(elf, symbol):
    objdump = None
    if os.environ.get('CONFIG_CAMKES_USE_OBJDUMP_ON', '') == 'y':
        objdump = '%sobjdump' % os.environ.get('TOOLPREFIX', '')
    elif os.environ.get('CONFIG_CAMKES_USE_OBJDUMP_AUTO', '') == 'y':
        with open(os.devnull, 'w') as f:
            try:
                objdump = subprocess.check_output(['which', '%sobjdump' %
                    os.environ.get('TOOLPREFIX', '')], stderr=f).strip()
            except subprocess.CalledProcessError:
                objdump = None
    if objdump is not None:
        global objdump_output
        stdout = objdump_output.get(elf[0])
        if stdout is None:
            # We haven't run objdump on this output yet. Need to do it now.
            # Construct the bash invocation we want
            argument = "%s --syms %s | grep -E '^[0-9a-fA-F]{8}' | sed -r 's/^([0-9a-fA-F]{8})[ \\t].*[ \\t]([0-9a-fA-F]{8})[ \\t]+(.*)/\\3 \\1 \\2/'" % (objdump, elf[0])
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

def set_tcb_info(cspaces, elfs, **_):
    '''Set relevant extra info for TCB objects.'''

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items() \
                if v is not None and isinstance(v.referent, TCB)]:

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

def set_tcb_caps(ast, obj_space, cspaces, elfs, options, **_):
    assembly = find_assembly(ast)

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items() \
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
                    if isinstance(cnode_size, str):
                        size = int(cnode_size, 0)
                    else:
                        size = cnode_size
                except ValueError:
                    raise Exception('illegal value for CNode size for %s' % \
                        group)
                if size < cnode.size_bits:
                    raise Exception('%d-bit CNode specified for %s, but this ' \
                        'CSpace needs to be at least %d bits' % \
                        (size, group, cnode.size_bits))
                cnode.size_bits = size

            cspace = Cap(cnode)
            cspace.set_guard_size(32 - cnode.size_bits)
            tcb['cspace'] = cspace

            elf_name = perspective['elf_name']

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

                tcb['ipc_buffer_slot'] = Cap(frame, True, True, False) # RW

            # Currently no fault EP (fault_ep_slot).

            # add SC 
            assembly = find_assembly(ast) 
            settings = assembly.configuration.settings if assembly.configuration is not None else []
            # first check if this thread has been configured to not have an SC
            passive_attribute_name = perspective['passive_attribute']
            instance_name = perspective['instance']
            passive_attributes = [x for x in settings if x.instance == instance_name and \
                                                         x.attribute == passive_attribute_name]

            # Determine whether a passive component instance thread was specified
            if len(passive_attributes) == 0:
                passive_instance = False
            elif len(passive_attributes) == 1:
                if passive_attributes[0].value is None:
                    passive_instance = False
                elif isinstance(passive_attributes[0].value, str):
                    passive_attribute = passive_attributes[0].value.lower()
                    if passive_attribute == 'true':
                        passive_instance = True
                    elif passive_attribute == 'false':
                        passive_instance = False
                    else:
                        raise Exception('Boolean string expected for %s.%s. Got "%s".' % (
                            instance_name, passive_attribute_name, passive_attribute))
                else:
                    raise Exception('Boolean string expected for %s.%s. Got "%s".' % (
                        instance_name, passive_attribute_name, passive_attributes[0].value))
            else:
                raise Exception('Multiple settings of attribute %s.%s.' % (
                    instance_name, passive_attribute_name))

            # Attach the SC to the component instance thread if it isn't passive
            if not passive_instance:
                sc_name = perspective['sc']
                scs = [x for x in obj_space.spec.objs if x.name == sc_name]
                if len(scs) == 0:
                    raise Exception('No SC found for active component instance %s' % instance_name)
                elif len(scs) > 1:
                    raise Exception('Multiple SCs found for %s' % group)
                else:
                    assert len(scs) == 1
                    sc, = scs
                    tcb['sc_slot'] = Cap(sc)

            # TODO add temp_fault_ep_slot


def collapse_shared_frames(ast, obj_space, elfs, options, **_):
    """Find regions in virtual address spaces that are intended to be backed by
    shared frames and adjust the capability distribution to reflect this."""

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    assembly = find_assembly(ast)

    # We want to track the frame objects backing shared regions with a dict
    # keyed on the name of the connection linking the regions.
    shared_frames = {}

    for i in (x for x in assembly.composition.instances
            if not x.type.hardware):

        perspective = Perspective(instance=i.name, group=i.address_space)

        elf_name = perspective['elf_name']
        assert elf_name in elfs
        elf = elfs[elf_name]

        # Find this instance's page directory.
        pd_name = perspective['pd']
        pds = [x for x in obj_space.spec.objs if x.name == pd_name]
        assert len(pds) == 1
        pd, = pds

        large_frame_uid = 0

        for d in i.type.dataports:

            # Find the connection that associates this dataport with another.
            connections = [x for x in assembly.composition.connections if \
                ((x.from_instance == i and x.from_interface == d) or \
                (x.to_instance == i and x.to_interface == d))]
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
            assert vaddr % PAGE_SIZE == 0, 'dataport %s not page-aligned' % sym
            sz = get_symbol_size(elf, sym)
            assert sz != 0

            arch = get_elf_arch(elf)

            # Infer the page table(s) and page(s) that back this region.
            pts, p_indices = zip(*[\
                (pd[page_table_index(arch, v)].referent,
                 page_index(arch, v)) \
                for v in xrange(vaddr, vaddr + sz, PAGE_SIZE)])

            # Determine the rights this mapping should have. We use these to
            # recreate the mapping below. Technically we may not need to
            # recreate this mapping if it's already correct, but do it anyway
            # for simplicity.
            # FIXME: stop hard coding this name mangling.
            rights_setting = assembly.configuration[conn_name].get('%s_access' % direction)
            if rights_setting is not None and \
                    re.match(r'^"R?W?(G|X)?"$', rights_setting):
                read = 'R' in rights_setting
                write = 'W' in rights_setting
                execute = 'X' in rights_setting or 'G' in rights_setting
            else:
                # default
                read = True
                write = True
                execute = False

            # Check if the dataport is connected *TO* a hardware component.
            if connections[0].to_instance.type.hardware:
                p = Perspective(to_interface=connections[0].to_interface.name)
                hardware_attribute = p['hardware_attribute']
                conf = assembly.configuration[connections[0].to_instance.name].get(hardware_attribute)
                assert conf is not None
                paddr, size = conf.strip('"').split(':')
                # Round up the MMIO size to PAGE_SIZE
                paddr = int(paddr, 0)
                size = int(size, 0)

                instance_name = connections[0].to_instance.name

                if size == 0:
                    raise Exception('Hardware dataport %s.%s has zero size!' % (instance_name,
                        connections[0].to_interface.name))

                # determine the size of a large frame, and the type of kernel
                # object that will be used, both of which depend on the architecture
                if get_elf_arch(elf) == 'ARM':
                    large_size = 1024 * 1024
                    large_object_type = seL4_ARM_SectionObject
                else:
                    large_size = 4 * 1024 * 1024
                    large_object_type = seL4_IA32_4M

                # Check if MMIO start and end is aligned to page table coverage.
                # This will indicate that we should use pagetable-sized pages
                # to back the device region to be consistent with the kernel.
                if paddr % large_size == 0 and size % large_size == 0:

                    # number of page tables backing device memory
                    n_pts = size / large_size

                    # index of first page table in page directory backing the device memory
                    base_pt_index = page_table_index(get_elf_arch(elf), vaddr)
                    pt_indices = xrange(base_pt_index, base_pt_index + n_pts)

                    # loop over all the page table indices and replace the page tables
                    # with large frames
                    for count, pt_index in enumerate(pt_indices):

                        # look up the page table at the current index
                        pt = pd[pt_index].referent

                        name = 'large_frame_%s_%d' % (instance_name, large_frame_uid)
                        large_frame_uid += 1

                        frame_paddr = paddr + large_size * count

                        # allocate a new large frame
                        frame = obj_space.alloc(large_object_type, name, paddr=frame_paddr)

                        # insert the frame cap into the page directory
                        frame_cap = Cap(frame, read, write, execute)
                        frame_cap.set_cached(False)
                        pd[pt_index] = frame_cap

                        # remove all the small frames from the spec
                        for p_index in pt:
                            small_frame = pt[p_index].referent
                            obj_space.remove(small_frame)

                        # remove the page table from the spec
                        obj_space.remove(pt)

                else:
                    # If the MMIO start and end are not aligned to page table coverage,
                    # loop over all the frames and set their paddrs based on the
                    # paddr in the spec.
                    for idx in xrange(0, (size + PAGE_SIZE - 1) / PAGE_SIZE):
                        try:
                            frame_obj = pts[idx][p_indices[idx]].referent
                        except IndexError:
                            raise Exception('MMIO attributes specify device ' \
                                'memory that is larger than the dataport it is ' \
                                'associated with')
                        frame_obj.paddr = paddr + PAGE_SIZE * idx
                        cap = Cap(frame_obj, read, write, execute)
                        cap.set_cached(False)
                        pts[idx].slots[p_indices[idx]] = cap
                        obj_space.relabel(conn_name, frame_obj)

                continue

            shm_keys = []
            for c in connections:
                shm_keys.append('%s_%s' % (c.from_instance.name, c.from_interface.name))
                shm_keys.append('%s_%s' % (c.to_instance.name, c.to_interface.name))

            mapped = [x for x in shm_keys if x in shared_frames]
            if mapped:
                # We've already encountered the other side of this dataport.

                # The region had better be the same size in all address spaces.
                for key in mapped:
                    assert len(shared_frames[key]) == sz / PAGE_SIZE

            # This is the first side of this dataport.

            # Save all the frames backing this region.
            for key in shm_keys:
                if mapped:
                    shared_frames[key] = shared_frames[mapped[0]]
                else:
                    shared_frames[key] = [pt[p_index].referent \
                        for (pt, p_index) in zip(pts, p_indices)]

            # Overwrite the caps backing this region with caps to the shared
            # frames.
            for j, f in enumerate(shared_frames[shm_keys[0]]):
                existing = pts[j].slots[p_indices[j]].referent
                if existing != f:
                    # We're actually modifying this mapping. Delete the
                    # unneeded frame.
                    obj_space.remove(existing)
                pts[j].slots[p_indices[j]] = Cap(f, read, write, execute)
                obj_space.relabel(conn_name, f)

def replace_dma_frames(ast, obj_space, elfs, options, **_):
    '''Locate the DMA pool (a region that needs to have frames whose mappings
    can be reversed) and replace its backing frames with pre-allocated,
    reversible ones.'''

    # TODO: Large parts of this function clagged from collapse_shared_frames; Refactor.

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    assembly = find_assembly(ast)

    for i in (x for x in assembly.composition.instances
            if not x.type.hardware):

        perspective = Perspective(instance=i.name, group=i.address_space)

        elf_name = perspective['elf_name']
        assert elf_name in elfs
        elf = elfs[elf_name]

        # Find this instance's page directory.
        pd_name = perspective['pd']
        pds = filter(lambda x: x.name == pd_name, obj_space.spec.objs)
        assert len(pds) == 1
        pd, = pds

        sym = perspective['dma_pool_symbol']
        base = get_symbol_vaddr(elf, sym)
        if base is None:
            # We don't have a DMA pool.
            continue
        assert base != 0
        sz = get_symbol_size(elf, sym)
        assert sz % PAGE_SIZE == 0 # DMA pool should be page-aligned.

        # Generate a list of the base addresses of the pages we need to
        # replace.
        base_vaddrs = [PAGE_SIZE * x + base for x in
            range(int(sz / PAGE_SIZE))]

        for index, v in enumerate(base_vaddrs):
            # Locate the mapping.
            pt_index = page_table_index(get_elf_arch(elf), v)
            p_index = page_index(get_elf_arch(elf), v)

            # It should contain an existing frame.
            assert pt_index in pd
            pt = pd[pt_index].referent
            assert p_index in pt
            discard_frame = pt[p_index].referent

            # Locate the frame we're going to replace it with. The logic that
            # constructs this object name is in component.template.c. Note that
            # we need to account for the guard-prefix of the instance name
            # introduced by the template context.
            p = Perspective(instance=i.name, group=i.address_space,
                dma_frame_index=index)
            dma_frames = [x for x in obj_space.spec.objs if
                x.name == p['dma_frame_symbol']]
            assert len(dma_frames) == 1
            dma_frame, = dma_frames

            # Replace the existing mapping.
            c = Cap(dma_frame, True, True, False) # RW
            c.set_cached(False)
            pt.slots[p_index] = c

            # We can now remove the old frame as we know it's not referenced
            # anywhere else. TODO: assert this somehow.
            obj_space.remove(discard_frame)

def guard_cnode_caps(cspaces, **_):
    '''If the templates have allocated any caps to CNodes, they will not have
    the correct guards. This is due to the CNodes' sizes being automatically
    calculated (during set_tcb_caps above). Correct them here.'''

    for space in cspaces.values():
        [cap.set_guard_size(32 - cap.referent.size_bits) \
            for cap in space.cnode.slots.values() \
            if cap is not None and isinstance(cap.referent, CNode)]

def guard_pages(obj_space, cspaces, elfs, options, **_):
    '''Introduce a guard page around each stack and IPC buffer. Note that the
    templates should have ensured a three page region for each stack in order to
    enable this.'''

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items() \
                if v is not None and isinstance(v.referent, TCB)]:

            perspective = Perspective(group=group, tcb=tcb.name)

            if perspective['pool']:
                # This TCB is part of the (cap allocator's) TCB pool.
                continue

            elf_name = perspective['elf_name']

            # Find the page directory.
            pd = None
            pd_name = perspective['pd']
            pds = [x for x in obj_space.spec.objs if x.name == pd_name]
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
                    raise Exception('IPC buffer region of TCB %s in group %s '
                        'does not appear to be backed by a page table' %
                        (tcb.name, group))
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
                obj_space.remove(frame)

                # Now do the same for the following guard page. We do this
                # calculation separately just in case the region crosses a PT
                # boundary and the two guard pages are in separate PTs.

                post_guard = pre_guard + 2 * PAGE_SIZE

                pt_index = page_table_index(get_elf_arch(elf), post_guard)
                if pt_index not in pd:
                    raise Exception('IPC buffer region of TCB %s in group %s '
                        'does not appear to be backed by a page table' %
                        (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), post_guard)
                if p_index not in pt:
                    raise Exception('IPC buffer region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

                # Now we do the same thing for the preceding guard page of the
                # thread's stack...

                stack_symbol = perspective['stack_symbol']

                pre_guard = get_symbol_vaddr(elf, stack_symbol)

                pt_index = page_table_index(get_elf_arch(elf), pre_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in group %s does '
                        'not appear to be backed by a page table' % (tcb.name,
                        group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), pre_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

                # ...and the following guard page.

                stack_region_size = get_symbol_size(elf, stack_symbol)
                assert stack_region_size % PAGE_SIZE == 0, \
                    'stack region is not page-aligned'
                assert stack_region_size >= 3 * PAGE_SIZE, \
                    'stack region has no room for guard pages'
                post_guard = pre_guard + stack_region_size - PAGE_SIZE

                pt_index = page_table_index(get_elf_arch(elf), post_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in group %s does '
                        'not appear to be backed by a page table' % (tcb.name,
                        group))
                pt = pd[pt_index].referent

                p_index = page_index(get_elf_arch(elf), post_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in ' \
                        'group %s does not appear to be backed by a frame' \
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

def tcb_default_priorities(obj_space, options, **_):
    '''Set up default thread priorities. Note this filter needs to operate
    *before* tcb_priorities.'''

    for t in [x for x in obj_space if isinstance(x, TCB)]:
        t.prio = options.default_priority
        t.max_prio = options.default_max_priority
        t.crit = options.default_criticality
        t.max_crit = options.default_max_criticality

def tcb_priorities(ast, cspaces, **_):
    ''' Override a TCB's default priority if the user has specified this in an
    attribute.'''

    assembly = find_assembly(ast)

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no priorities were set.
        return

    for group, space in cspaces.items():
        cnode = space.cnode
        for tcb in [v.referent for v in cnode.slots.values() \
                if v is not None and isinstance(v.referent, TCB)]:

            perspective = Perspective(group=group, tcb=tcb.name)

            # Find the priority if it was set.
            prio_attribute = perspective['priority_attribute']
            name = perspective['instance']
            prio = assembly.configuration[name].get(prio_attribute)
            if prio is not None:
                tcb.prio = prio
            else:
                # See if the user assigned a general priority to this component.
                prio = assembly.configuration[name].get('priority')
                if prio is not None:
                    tcb.prio = prio

            # Find the max_priority if it was set.
            max_prio_attribute = perspective['max_priority_attribute']
            name = perspective['instance']
            max_prio = assembly.configuration[name].get(max_prio_attribute)
            if max_prio is not None:
                tcb.max_prio = max_prio

            # Find the criticality if it was set.
            crit_attribute = perspective['criticality_attribute']
            name = perspective['instance']
            crit =  assembly.configuration[name].get(crit_attribute)
            if crit is not None:
                tcb.crit = crit

            # Find the max_criticality if it was set.
            max_crit_attribute = perspective['max_criticality_attribute']
            name = perspective['instance']
            max_crit = assembly.configuration[name].get(max_crit_attribute)
            if max_crit is not None:
                tcb.max_crit = max_crit

def tcb_domains(ast, cspaces, **_):
    '''Set the domain of a TCB if the user has specified this in an
    attribute.'''

    assembly = find_assembly(ast)

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no domains were set.
        return

    for group, space in cspaces.items():
        cnode = space.cnode
        for tcb in [x.referent for x in cnode.slots.values() if \
                (x is not None and isinstance(x.referent, TCB))]:

            perspective = Perspective(group=group, tcb=tcb.name)

            # Find the domain if it was set.
            dom_attribute = perspective['domain_attribute']
            name = perspective['instance']
            dom = assembly.configuration[name].get(dom_attribute)
            if dom is not None:
                tcb.domain = dom

def remove_tcb_caps(cspaces, options, **_):
    '''Remove all TCB caps in the system if requested by the user.'''
    if not options.fprovide_tcb_caps:
        for space in cspaces.values():
            for slot in [k for (k, v) in space.cnode.slots.items() \
                    if v is not None and isinstance(v.referent, TCB)]:
                del space.cnode[slot]


def sc_default_properties(ast, obj_space, cspaces, elfs, options, shmem):
    '''Set up default scheduling context properties. Note this filter needs to operate
    *before* sc_properties.'''

    for s in filter(lambda x: isinstance(x, SC), obj_space):
        s.period = options.default_period
        s.budget = options.default_budget
        s.data = options.default_data

def sc_properties(ast, obj_space, cspaces, elfs, options, shmem):
    ''' Override an SC's default properties if the user has specified this in an
    attribute.'''

    assembly = find_assembly(ast)

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no properties were set.
        return

    settings = assembly.configuration.settings

    for group, space in cspaces.items():
        cnode = space.cnode
        for cap in cnode.slots.values():

            if cap is None:
                continue
            sc = cap.referent
            if not isinstance(sc, SC):
                continue

            perspective = Perspective(group=group, sc=sc.name)

            # Find the period if it was set.
            period_attribute = perspective['period_attribute']
            name = perspective['instance']
            period = assembly.configuration[name].get(period_attribute)
            if period is not None:
                sc.period = period

            # Find the budget if it was set.
            budget_attribute = perspective['budget_attribute']
            name = perspective['instance']
            budget = assembly.configuration[name].get(budget_attribute)
            if budget is not None:
                sc.budget = budget

            # Find the data if it was set.
            data_attribute = perspective['data_attribute']
            name = perspective['instance']
            data = assembly.configuration[name].get(data_attribute)
            if data is not None:
                sc.data = data

CAPDL_FILTERS = [
    set_tcb_info,
    set_tcb_caps,
    collapse_shared_frames,
    replace_dma_frames,
    guard_cnode_caps,
    guard_pages,
    tcb_default_priorities,
    tcb_priorities,
    tcb_domains,
    remove_tcb_caps,
    sc_default_properties,
    sc_properties,
]
