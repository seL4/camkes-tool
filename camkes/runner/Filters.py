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

'''Filters to be applied to generated CapDL.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import os, re, six, subprocess
from capdl import Cap, CNode, Frame, TCB, page_index, page_sizes, \
    page_table_coverage, page_table_index
from camkes.internal.memoization import memoize
from NameMangling import Perspective

PAGE_SIZE = 4096 # bytes
IPC_BUFFER_SIZE = 512 # bytes

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
            argument = "%s --syms %s | grep -E '^[0-9a-fA-F]{8}' | sed -r 's/^([0-9a-fA-F]{8})[ \\t].*[ \\t]([0-9a-fA-F]{8})[ \\t]+(.*)/\\3 \\1 \\2/'" % (objdump, elf[0])
            stdout = subprocess.check_output(['sh', '-c', argument],
                universal_newlines=True)
            # Cache the result for future symbol lookups.
            objdump_output[elf[0]] = stdout
        sym_index = stdout.find('\n%s ' % symbol)
        if sym_index == -1:
            return None, None
        vaddr_index = sym_index + len(symbol) + 2
        size_index = vaddr_index + 9
        return int(stdout[vaddr_index:vaddr_index+8], 16), \
            int(stdout[size_index:size_index+8], 16)
    else:
        return elf[1].get_symbol_vaddr(symbol), elf[1].get_symbol_size(symbol)

def get_symbol_vaddr(elf, symbol):
    return get_symbol(elf, symbol)[0]
def get_symbol_size(elf, symbol):
    return get_symbol(elf, symbol)[1]
def get_elf_arch(elf):
    return elf[1].get_arch()

def set_tcb_info(cspaces, elfs, **_):
    '''Set relevant extra info for TCB objects.'''

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
                2 * PAGE_SIZE - IPC_BUFFER_SIZE

            # Each TCB needs to be passed its 'thread_id' that is the value
            # it branches on in main(). This corresponds to the slot index
            # to a cap to it in the component's CNode.
            tcb.init.append(index)

def set_tcb_caps(ast, obj_space, cspaces, elfs, options, **_):
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
                pt_index = page_table_index(options.architecture, ipc_vaddr)
                if pt_index not in pd:
                    raise Exception('IPC buffer of TCB %s in group %s does '
                        'not appear to be backed by a page table' % (tcb.name, group))
                pt = pd[pt_index].referent

                # Continue on to infer the physical frame.
                p_index = page_index(options.architecture, ipc_vaddr)
                if p_index not in pt:
                    raise Exception('IPC buffer of TCB %s in group %s does '
                        'not appear to be backed by a frame' % (tcb.name, group))
                frame = pt[p_index].referent

                tcb['ipc_buffer_slot'] = Cap(frame, True, True, False) # RW

            # Optional fault endpoints are configured in the per-component
            # template.

def collapse_shared_frames(ast, obj_space, elfs, shmem, options, **_):
    """Find regions in virtual address spaces that are intended to be backed by
    shared frames and adjust the capability distribution to reflect this."""

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    assembly = ast.assembly

    large_frame_size = None

    for window, mappings in shmem.items():
        frames = None
        for cnode, local_mappings in mappings.items():
            for sym, permissions, paddr in local_mappings:

                perspective = Perspective(cnode=cnode)

                # Find this instance's ELF file.
                elf_name = perspective['elf_name']
                assert elf_name in elfs
                elf = elfs[elf_name]

                # Find this instance's page directory.
                pd_name = perspective['pd']
                pds = [x for x in obj_space.spec.objs if x.name == pd_name]
                assert len(pds) == 1
                pd = pds[0]

                # Look up the ELF-local version of this symbol.
                vaddr = get_symbol_vaddr(elf, sym)
                assert vaddr is not None, 'shared symbol \'%s\' not found in ' \
                    'ELF %s (template bug?)' % (sym, elf_name)
                assert vaddr != 0, 'shared symbol \'%s\' located at NULL in ELF ' \
                    '%s (template bug?)' % (sym, elf_name)
                assert vaddr % PAGE_SIZE == 0, 'shared symbol \'%s\' not ' \
                    'page-aligned in ELF %s (template bug?)' % (sym, elf_name)

                size = get_symbol_size(elf, sym)
                assert size != 0, 'shared symbol \'%s\' has size 0 in ELF %s ' \
                    '(template bug?)' % (sym, elf_name)
                assert size % PAGE_SIZE == 0, 'shared symbol \'%s\' in ELF %s ' \
                    'has a size that is not page-aligned (template bug?)' % \
                    (sym, elf_name)

                # Different architectures have different large frame sizes. We will
                # need these later if this window is device registers or should be
                # promoted to large frames.
                if options.architecture == 'arm_hyp':
                    large_frame_size = 2 * 1024 * 1024 # 2M
                elif options.architecture == 'arm':
                    large_frame_size = 1024 * 1024 # 1M
                else:
                    assert options.architecture == 'ia32'
                    large_frame_size = 4 * 1024 * 1024 # 4M

                # Infer the page table(s) and small page(s) that currently back this
                # region.
                map_indices = [(page_table_index(options.architecture, v),
                                page_index(options.architecture, v))
                    for v in six.moves.range(vaddr, vaddr + size, PAGE_SIZE)]

                # Permissions that we will apply to the eventual mapping.
                read = 'R' in permissions
                write = 'W' in permissions
                execute = 'X' in permissions

                if frames is None:
                    # First iteration of the loop; we need to discover the backing
                    # frames for this region.
                    frames = []

                    # We want to derive large frames if (a) this window is device
                    # registers and large-frame-sized (in which case the kernel
                    # will have created it as large frames) or (b) the user has
                    # requested large frame promotion. Note that we never promote
                    # shared memory windows to anything larger than large frames.
                    if vaddr % large_frame_size == 0 and \
                            size % large_frame_size == 0 and \
                            (options.largeframe or paddr is not None):

                        assert paddr is None or paddr % large_frame_size == 0, \
                            'unaligned physical address of large device'

                        # Iterate over the unique page table indices.
                        seen = set()
                        for offset, index in enumerate((pt_index for pt_index, _
                                in map_indices if
                                not (pt_index in seen or seen.add(pt_index)))):

                            pt = pd[index].referent

                            # Delete all the underlying small frames, saving
                            # the first to enlarge and re-insert.
                            frame = None
                            for cap in pt.values():
                                if frame is None:
                                    frame = cap.referent
                                obj_space.remove(cap.referent)
                            assert frame is not None, 'a page table covering a ' \
                                'shared memory region was unexpectedly empty ' \
                                '(filter bug?)'

                            # Delete the page table itself.
                            obj_space.remove(pt)

                            # Replace it with a large frame.
                            frame.size = large_frame_size
                            cap = Cap(frame, read, write, execute)
                            if paddr is not None:
                                frame.paddr = paddr + offset * large_frame_size
                                cap.set_cached(False)
                            pd[index] = cap

                            frames.append(frame)

                    else:
                        # We don't need to handle large frame promotion. Just tweak
                        # the permissions and optionally the physical address of
                        # all the current mappings.
                        for offset, (pt_index, p_index) in enumerate(map_indices):
                            cap = pd[pt_index].referent[p_index]
                            frame = cap.referent
                            cap.read = read
                            cap.write = write
                            cap.grant = execute
                            if paddr is not None:
                                frame.paddr = paddr + offset * PAGE_SIZE
                                cap.set_cached(False)

                            frames.append(frame)

                else:
                    # We have already discovered frames to back this region and now
                    # we just need to adjust page table mappings.

                    assert size == sum(f.size for f in frames), 'mismatched ' \
                        'sizes of shared region \'%s\' (template bug?)' % window

                    offset = 0
                    for frame in frames:
                        pt_index = page_table_index(options.architecture,
                            vaddr + offset)

                        if frame.size == large_frame_size:
                            # The window has been promoted to large frames.

                            pt = pd[pt_index].referent

                            # Delete all the underlying small frames.
                            [obj_space.remove(cap.referent) for cap in pt.values()]

                            # Delete the page table itself.
                            obj_space.remove(pt)

                            # Replace it with the large frame we previously saved.
                            cap = Cap(frame, read, write, execute)
                            if paddr is not None:
                                cap.set_cached(False)
                            pd[index] = cap

                        else:
                            # The window has not been promoted to large frames.

                            assert frame.size == PAGE_SIZE

                            p_index = page_index(options.architecture,
                                vaddr + offset)
                            obj_space.remove(pd[pt_index].referent[p_index].referent)
                            cap = Cap(frame, read, write, execute)
                            if paddr is not None:
                                cap.set_cached(False)
                            pd[pt_index].referent[p_index] = cap

                        offset += frame.size

def replace_dma_frames(ast, obj_space, elfs, options, **_):
    '''Locate the DMA pool (a region that needs to have frames whose mappings
    can be reversed) and replace its backing frames with pre-allocated,
    reversible ones.'''

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    assembly = ast.assembly

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

        sym = perspective['dma_pool_symbol']
        base = get_symbol_vaddr(elf, sym)
        if base is None:
            # We don't have a DMA pool.
            continue
        assert base != 0
        sz = get_symbol_size(elf, sym)
        assert sz % PAGE_SIZE == 0 # DMA pool should be at least page-aligned.

        # Replicate logic from the template to determine the page size used to
        # back the DMA pool.
        page_size = 4 * 1024
        if options.largeframe_dma:
            for size in reversed(page_sizes(options.architecture)):
                if sz >= size:
                    page_size = size
                    break

        assert sz % page_size == 0, 'DMA pool not rounded up to a multiple ' \
            'of page size %d (template bug?)' % page_size

        dma_frame_index = 0
        def get_dma_frame(index):
            '''
            Find the `index`-th DMA frame. Note that these are constructed in
            the component template itself.
            '''
            p = Perspective(instance=i.name, group=i.address_space,
                dma_frame_index=index)
            dma_frames = [x for x in obj_space.spec.objs if
                x.name == p['dma_frame_symbol']]
            assert len(dma_frames) == 1
            dma_frame = dma_frames[0]
            return dma_frame

        for index, v in enumerate(page_size * x + base for x in
                six.moves.range(sz // page_size)):
            # Locate the existing mapping.
            pt_index = page_table_index(options.architecture, v)
            p_index = page_index(options.architecture, v)

            # The size of a page table.
            pt_size = page_table_coverage(options.architecture)

            # The existing mapping should contain at least one frame.
            assert pt_index in pd
            pt = pd[pt_index].referent
            assert p_index in pt

            # There are four possible scenarios here:
            #  1. The page size used to back the DMA pool is greater than the
            #     size of a page table, so frames need to be mapped directly
            #     into the page directory, evicting multiple page tables;
            #  2. The page size used to back the DMA pool is equal to the size
            #     of a page table, so frames need to be mapped directly into
            #     the page directory, evicting a single page table;
            #  3. The page size used to back the DMA pool is smaller than a
            #     page table, but larger than 4KB, so frames need to be mapped
            #     into page tables, evicting multiple existing pages;
            #  4. The page size used to back the DMA pool is 4KB, so frames
            #     need to be mapped into page tables, evicting single existing
            #     pages.
            # This loop is intended to handle all these cases, with the
            # conditional code inside the loop taking care of a subset of
            # these.
            for pt_offset in six.moves.range((page_size // pt_size) or 1):

                # Find the covering page table.
                pt_vaddr = v + page_size * pt_offset
                pt_index = page_table_index(options.architecture, pt_vaddr)
                assert pt_index in pd
                pt = pd[pt_index].referent

                # For each page in this page table...
                for p_offset in six.moves.range(min(pt_size, page_size) //
                        PAGE_SIZE):

                    # Find the existing page mapping.
                    p_vaddr = pt_vaddr + PAGE_SIZE * p_offset
                    p_index = page_index(options.architecture, p_vaddr)
                    assert p_index in pt
                    p = pt[p_index].referent

                    # Delete it.
                    del pt[p_index]
                    obj_space.remove(p)

                    # If the DMA pool is backed by frames that need to be
                    # mapped into page tables and we're at an appropriately
                    # aligned address, install a mapping.
                    if page_size < pt_size and p_vaddr % page_size == 0:
                        f = get_dma_frame(dma_frame_index)
                        assert f.size == page_size, 'DMA frame found with ' \
                            'unexpected size %d instead of %d (template bug?)' \
                            % (f.size, page_size)
                        dma_frame_index += 1
                        c = Cap(f, True, True, False) # RW
                        c.set_cached(False)
                        pt[p_index] = c

                # If the DMA pool is backed by frames larger than a page table,
                # we need to delete the covering page table(s) itself.
                if page_size >= pt_size:
                    del pd[pt_index]
                    obj_space.remove(pt)

                    # If we're at an appropriately aligned address, install a
                    # large frame mapping.
                    if pt_vaddr % page_size == 0:
                        f = get_dma_frame(dma_frame_index)
                        assert f.size == page_size, 'DMA frame found with ' \
                            'unexpected size %d instead of %d (template bug?)' \
                            % (f.size, page_size)
                        dma_frame_index += 1
                        c = Cap(f, True, True, False) # RW
                        c.set_cached(False)
                        pd[pt_index] = c

def guard_cnode_caps(cspaces, **_):
    '''If the templates have allocated any caps to CNodes, they will not have
    the correct guards. This is due to the CNodes' sizes being automatically
    calculated (during set_tcb_caps above). Correct them here.'''

    for space in cspaces.values():
        [cap.set_guard_size(32 - cap.referent.size_bits)
            for cap in space.cnode.slots.values()
            if cap is not None and isinstance(cap.referent, CNode)]

def guard_pages(obj_space, cspaces, elfs, options, **_):
    '''Introduce a guard page around each stack and IPC buffer. Note that the
    templates should have ensured a three page region for each stack in order to
    enable this.'''

    for group, space in cspaces.items():
        cnode = space.cnode
        for index, tcb in [(k, v.referent) for (k, v) in cnode.slots.items()
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
                pt_index = page_table_index(options.architecture, pre_guard)
                if pt_index not in pd:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                # Continue on to infer the page.
                p_index = page_index(options.architecture, pre_guard)
                if p_index not in pt:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                # Delete the page.
                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

                # Now do the same for the following guard page. We do this
                # calculation separately just in case the region crosses a PT
                # boundary and the two guard pages are in separate PTs.

                post_guard = pre_guard + 2 * PAGE_SIZE

                pt_index = page_table_index(options.architecture, post_guard)
                if pt_index not in pd:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(options.architecture, post_guard)
                if p_index not in pt:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

                # Now we do the same thing for the preceding guard page of the
                # thread's stack...

                stack_symbol = perspective['stack_symbol']

                pre_guard = get_symbol_vaddr(elf, stack_symbol)

                pt_index = page_table_index(options.architecture, pre_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(options.architecture, pre_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
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

                pt_index = page_table_index(options.architecture, post_guard)
                if pt_index not in pd:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))
                pt = pd[pt_index].referent

                p_index = page_index(options.architecture, post_guard)
                if p_index not in pt:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                frame = pt[p_index].referent
                del pt[p_index]
                obj_space.remove(frame)

def tcb_default_priorities(obj_space, options, **_):
    '''Set up default thread priorities. Note this filter needs to operate
    *before* tcb_priorities.'''

    for t in [x for x in obj_space if isinstance(x, TCB)]:
        t.prio = options.default_priority

def tcb_priorities(ast, cspaces, options, **_):
    ''' Override a TCB's default priority if the user has specified this in an
    attribute.'''

    assembly = ast.assembly

    if assembly.configuration is None or \
            len(assembly.configuration.settings) == 0:
        # We have nothing to do if no priorities were set.
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

def tcb_domains(ast, cspaces, **_):
    '''Set the domain of a TCB if the user has specified this in an
    attribute.'''

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
    '''Remove all TCB caps in the system if requested by the user.'''
    if not options.fprovide_tcb_caps:
        for space in cspaces.values():
            for slot in [k for (k, v) in space.cnode.slots.items()
                    if v is not None and isinstance(v.referent, TCB)]:
                del space.cnode[slot]

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
]
