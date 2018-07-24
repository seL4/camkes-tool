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

'''Filters to be applied to generated CapDL.'''
from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

import os, re, six, subprocess
from capdl import seL4_FrameObject, Cap, CNode, Frame, TCB, SC, page_sizes, lookup_architecture
from capdl.util import IA32Arch, X64Arch
from camkes.internal.memoization import memoize
from .NameMangling import Perspective

PAGE_SIZE = 4096 # bytes

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
            argument = "%s --syms %s | grep -E '^[0-9a-fA-F]{8}' | sed -r 's/^([0-9a-fA-F]{8,})[ \\t].*[ \\t]([0-9a-fA-F]{8,})[ \\t]+(.*)/\\3 \\1 \\2/'" % (objdump, elf[0])
            stdout = subprocess.check_output(['sh', '-c', argument],
                universal_newlines=True)
            # Cache the result for future symbol lookups.
            objdump_output[elf[0]] = stdout
        sym_index = stdout.find('\n%s ' % symbol)
        if sym_index == -1:
            return None, None
        end_index = stdout[sym_index+1:].find('\n')
        vaddr_start_index = sym_index + len(symbol) + 2
        if end_index == -1:
            substring = stdout[vaddr_start_index:]
        else:
            substring = stdout[vaddr_start_index:sym_index + end_index + 1]
        [vaddr, size] = substring.split()
        return int(vaddr, 16), int(size, 16)
    else:
        return elf[1].get_symbol_vaddr(symbol), elf[1].get_symbol_size(symbol)

def get_symbol_vaddr(elf, symbol):
    return get_symbol(elf, symbol)[0]
def get_symbol_size(elf, symbol):
    return get_symbol(elf, symbol)[1]
def get_elf_arch(elf):
    return elf[1].get_arch()

def set_tcb_info(cspaces, obj_space, elfs, options, **_):
    '''Set relevant extra info for TCB objects.'''
    arch = lookup_architecture(options.architecture)

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
                2 * PAGE_SIZE - arch.ipc_buffer_size()

            # Each TCB needs to be passed its 'thread_id' that is the value
            # it branches on in main(). This corresponds to the slot index
            # to a cap to it in the component's CNode.
            tcb.init.append(index)

            if options.realtime:
                sc_name = perspective['sc']
                if sc_name in obj_space:
                    # For non-passive threads, associate the sc with the tcb
                    sc = obj_space[sc_name]
                    tcb['sc_slot'] = Cap(sc)

def make_indices(arch, vaddr, size):
    '''Construct a set of indices that could be used to traverse to the mapping
       at the given vaddr for some concrete set of vspace objects. The size
       is used to determine how many levels need to be traversed'''
    level = arch.vspace()
    indices = []
    assert size < level.coverage, "Object is bigger than virtual address space. Your ELF is probably corrupt"
    while level.child is not None and size < level.child.coverage:
        level = level.child
        index = level.parent_index(vaddr)
        indices.append(index)
    indices.append(level.child_index(vaddr))
    return indices

def lookup_vspace_indices(vspace_root, indices):
    '''Takes a set of indices (of the form generated by make_indices) and
       traverses the supplied vspace_root, returning the cap and object found'''
    assert len(indices) > 0, "The root vspace object cannot be indexed, as we cannot return a capability to it"
    cap = None
    object = vspace_root
    for index in indices:
        cap = object[index]
        object = cap.referent
    return (cap, object)

def update_frame_in_vaddr(arch, vspace_root, vaddr, size, cap):
    '''Updates a frame mapping in a virtual address space. The semantics
       of what this is doing is such that after performing this then
       lookup_cap, _ = lookup_vspace_indices(vspace_root, make_indices(arch, vaddr,size))
       Gives lookup_cap == cap'''
    indices = make_indices(arch, vaddr, size)
    object = vspace_root
    for index in indices[0:-1]:
        object = object[index].referent
    object[indices[-1]] = cap

def frame_for_vaddr(arch, vspace_root, vaddr, size):
    '''Looks up a frame of a given size in a vspace hierarchy, returning
       the cap and object'''
    cap, object = lookup_vspace_indices(vspace_root, make_indices(arch, vaddr, size))
    assert isinstance(object, Frame), "Expected to find a frame"
    return cap, object

def num_vspace_levels(arch):
    '''Return the number of levels in the vspace hierarchy'''
    level = arch.vspace()
    level_num = 0
    while level is not None:
        level_num = level_num + 1
        level = level.child
    return level_num

def find_optimal_frame_size(arch, vaddr, size):
    '''Finds the largest frame supported by this architecture for a frame of the
       specified size at the given virtual address, returning this size and which
       vspace level it should be mapped at.'''
    level = arch.vspace()
    # Start at 1 as a frame cannot replace the top level object
    level_num = 1
    while level is not None:
        matched_size = 0
        for page in level.pages:
            if vaddr % page.size == 0 and size % page.size == 0 and page.size > matched_size:
                matched_size = page.size
        if matched_size != 0:
            return (matched_size, level_num)
        level = level.child
        level_num = level_num + 1
    raise Exception('Failed to find valid frame size for frame at %x of size %d' % (vaddr, size))

def delete_small_frames(arch, obj_space, vspace_root, level_num, map_indices):
    '''Given a set of indices (map_indices) that correspond to frames in the supplied
       vspace, this function removes all of the frames from the vspace, as well as any
       intermediate paging structures specified by the indecies, such that new frames
       (or anything else) can no be placed straight at the level indicated by level_num'''
    level = num_vspace_levels(arch)
    while level >= level_num:
        for indices in map_indices:
            sub_indices = indices[0:level]
            parent_indices = sub_indices[0:-1]
            if len(parent_indices) == 0:
                # parent is vspace root
                parent_object = vspace_root
            else:
                (parent_cap, parent_object) = lookup_vspace_indices(vspace_root, parent_indices)

            cap = parent_object[sub_indices[-1]]

            if cap is None:
                # it's possible that this table entry was removed in a previous iteration
                continue

            object = cap.referent
            if object is not None:
                obj_space.remove(object)
                parent_object[sub_indices[-1]] = None
        level = level - 1

def make_indices_to_frame(arch, vspace_root, vaddr):
    '''Given the root paging structure of a vspace, and a vaddr in that vspace,
       constructs a list of indices to traverse the paging hierarchy from the root
       to the frame containing the vaddr.'''
    level = arch.vspace()
    assert level.make_object == type(vspace_root), "vspace root must be top of page hierarchy"
    levels = []
    obj = vspace_root
    cap = None

    while not isinstance(obj, Frame):
        index = level.child_index(vaddr)

        levels.append((level, index))

        level = level.child
        cap = obj[index]
        obj = cap.referent

    return cap, levels

def replace_frame_with_paging_structure(obj_space, vspace_root, frame_cap, bottom_level, indices):
    '''Given the root paging structure of a vspace, a cap to a frame in that vspace,
       a list of indices to traverse the paging hierarchy from the root to the that frame,
       and the level of the paging hierarchy containing the frame, replaces the frame with
       a paging structure of the same size, and populates it with appropriately sized frames.'''

    assert len(indices) >= 1, "Empty list of indices"

    paging_structure = obj_space.alloc(bottom_level.object)
    child_size = min(p.size for p in bottom_level.pages)

    # populate the paging structure with new frames
    for i in range(0, bottom_level.coverage // child_size):
        new_frame = obj_space.alloc(seL4_FrameObject, size=child_size)
        paging_structure[i] = Cap(new_frame, frame_cap.read, frame_cap.write, frame_cap.grant)

    # find the parent paging structure
    if len(indices) == 1:
        parent = vspace_root
    else:
        _, parent = lookup_vspace_indices(vspace_root, indices[0:-1])

    # replace the entry in the parent
    parent[indices[-1]] = Cap(paging_structure, frame_cap.read, frame_cap.write, frame_cap.grant)

    # delete the old frame
    obj_space.remove(frame_cap.referent)

def replace_frame_with_small_frames(obj_space, vspace_root, frame_cap, bottom_level, indices):
    '''Given the root paging structure of a vspace, a cap to a frame in that vspace,
       a list of indices to traverse the paging hierarchy from the root to the that frame,
       and the level of the paging hierarchy containing the frame, replaces the frame with
       a collection of smaller frames, mapped into the same paging structure.'''

    assert len(indices) >= 1, "Empty list of indices"

    # look up the paging structure containing the frame that we'll be replacing
    if len(indices) == 1:
        paging_structure = vspace_root
    else:
        _, paging_structure = lookup_vspace_indices(vspace_root, indices[0:-1])

    # index of the frame we're replacing in its paging structure
    start_index = indices[-1]

    assert paging_structure[start_index] == frame_cap, "Unexpected frame cap"

    old_frame_size = frame_cap.referent.size
    new_frame_size = min(p.size for p in bottom_level.pages)

    assert old_frame_size % new_frame_size == 0, "Small frame size does not evenly divide larger frame size"

    num_frames = old_frame_size // new_frame_size

    # create new frames and map them in
    for i in range(0, num_frames):
        new_frame = obj_space.alloc(seL4_FrameObject, size=new_frame_size)
        paging_structure[start_index + i] = Cap(new_frame, frame_cap.read, frame_cap.write, frame_cap.grant)

    obj_space.remove(frame_cap.referent)

def replace_large_frames(obj_space, arch, vspace_root, start_vaddr, size, page_size):
    '''Given the root paging structure of a vspace, and a virtual address range, replaces
       all frames with frames of the given (smaller) size, creating necessary intermediate
       paging structures.'''
    offset = 0
    while offset < size:
        vaddr = start_vaddr + offset
        frame_cap, levels = make_indices_to_frame(arch, vspace_root, vaddr)

        if frame_cap.referent.size <= page_size:
            # Found frame of desired size - keep going.
            offset += page_size
        else:
            # Found a large frame - replace it.
            # Note that we don't increment the offset here, as we may
            # have to replace the frame with even smaller frames.

            # extract a list of indices from the list of (level, index) tuples
            indices = [l[1] for l in levels]

            (bottom_level, _) = levels[-1]
            if bottom_level.child is not None and bottom_level.child.coverage == frame_cap.referent.size:
                # This large frame can be replaced with a paging structure
                # of the same coverage.
                replace_frame_with_paging_structure(obj_space, vspace_root, frame_cap, bottom_level.child, indices)
            else:
                # This large frame can be replace by smaller frames in
                # the same paging structure.
                replace_frame_with_small_frames(obj_space, vspace_root, frame_cap, bottom_level, indices)

def set_tcb_caps(ast, obj_space, cspaces, elfs, options, **_):
    arch = lookup_architecture(options.architecture)
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
            cspace.set_guard_size(arch.word_size_bits() - cnode.size_bits)
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

                # Find the frame for this
                (cap, frame) = frame_for_vaddr(arch, pd, ipc_vaddr, PAGE_SIZE)
                if frame is None:
                    raise Exception('IPC buffer of TCB %s in group %s does ' \
                        'not appear to be backed by a frame' % (tcb.name, group))

                tcb['ipc_buffer_slot'] = Cap(frame, True, True, False) # RW

            # Optional fault endpoints are configured in the per-component
            # template.

def collapse_shared_frames(ast, obj_space, elfs, shmem, options, **_):
    """Find regions in virtual address spaces that are intended to be backed by
    shared frames and adjust the capability distribution to reflect this."""

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    arch = lookup_architecture(options.architecture)
    assembly = ast.assembly

    for window, mappings in shmem.items():
        frames = None
        exact_frames = False

        # If the shared variable has an associated set of backing frames
        # allocated already (ie. allocated in a template), look it up
        # before collapsing the shared variable.
        for mapping in mappings.values():
            for _, _, _, prealloc_frames, _ in mapping:
                if prealloc_frames is not None:
                    assert frames is None, 'Multiple sides of shared memory with' \
                            'preallocated frames for shared variable "%s"' % window

                    frames = prealloc_frames
                    exact_frames = True

        for cnode, local_mappings in mappings.items():
            for sym, permissions, paddr, _, cached_hw in local_mappings:

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

                # Infer the page table(s) and small page(s) that currently back this
                # region.
                map_indices = [make_indices(arch, v, PAGE_SIZE)
                    for v in six.moves.range(vaddr, vaddr + size, PAGE_SIZE)]

                # Permissions that we will apply to the eventual mapping.
                read = 'R' in permissions
                write = 'W' in permissions
                execute = 'X' in permissions

                largest_frame_size, level_num = find_optimal_frame_size(arch, vaddr, size)

                if frames is None:
                    # First iteration of the loop; we need to discover the backing
                    # frames for this region.
                    frames = []

                    # We want to derive large frames if (a) this window is device
                    # registers and large-frame-sized (in which case the kernel
                    # will have created it as large frames) or (b) the user has
                    # requested large frame promotion.
                    if largest_frame_size != PAGE_SIZE and (options.largeframe or paddr is not None):
                        # Grab a copy of the frame for every entry we're going to end up making
                        new_frames = {}
                        for new_vaddr in six.moves.range(vaddr, vaddr + size, largest_frame_size):
                            new_frames[new_vaddr] = obj_space.alloc(seL4_FrameObject, size=largest_frame_size)
                        # Iterate over every unique index in every object below this one
                        delete_small_frames(arch, obj_space, pd, level_num, map_indices)
                        # Now insert the new frames
                        for new_vaddr in six.moves.range(vaddr, vaddr + size, largest_frame_size):
                            frame = new_frames[new_vaddr]
                            cap = Cap(frame, read, write, execute)
                            if paddr is not None:
                                frame.paddr = paddr + (new_vaddr - vaddr)
                                cap.set_cached(cached_hw)
                            update_frame_in_vaddr(arch, pd, new_vaddr, largest_frame_size, cap)
                            frames.append(frame)

                    else:
                        # We don't need to handle large frame promotion. Just tweak
                        # the permissions and optionally the physical address of
                        # all the current mappings.
                        for offset, indices in enumerate(map_indices):
                            (cap, frame ) = lookup_vspace_indices(pd, indices)
                            cap.read = read
                            cap.write = write
                            cap.grant = execute
                            if paddr is not None:
                                frame.paddr = paddr + offset * PAGE_SIZE
                                cap.set_cached(cached_hw)
                            frames.append(frame)

                else:
                    # We have already discovered frames to back this region and now
                    # we just need to adjust page table mappings.

                    assert size == sum(f.size for f in frames), 'mismatched ' \
                        'sizes of shared region \'%s\' (template bug?)' % window

                    if not exact_frames:
                        # We do not need to preserve the exact same frames / frame sizings, so
                        # we can delete the entire region ready to put in our new frames
                        # Delete all the underlying frames / objects for this range
                        delete_small_frames(arch, obj_space, pd, level_num, map_indices)
                    offset = 0
                    for frame in frames:
                        cap = Cap(frame, read, write, execute)
                        if paddr is not None:
                            cap.set_cached(cached_hw)
                        if exact_frames:
                            # If we need to preserve the exact frames then we need to clear
                            # the range for each frame individually, up to the required level
                            # for that frame. This is to allow for 'weird' shared memory regions
                            # that have preallocated frames with different sized frames in
                            # the one region.
                            frame_map_indices = [make_indices(arch, v, PAGE_SIZE)
                                for v in six.moves.range(vaddr + offset, vaddr + offset + frame.size, PAGE_SIZE)]
                            _, frame_level_num = find_optimal_frame_size(arch, 0, frame.size)
                            delete_small_frames(arch, obj_space, pd, frame_level_num, frame_map_indices)
                        # Now, with exact_frames or not, we know that the slot for this frame is
                        # free and we can re-insert the correct frame
                        update_frame_in_vaddr(arch, pd, vaddr + offset, frame.size, cap)
                        offset = offset + frame.size

def describe_fill_frames(ast, obj_space, elfs, fill_frames, options, **_):

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    arch = lookup_architecture(options.architecture)
    assembly = ast.assembly

    for name in fill_frames:
        # Find it in assembly.composition.instances?
        instances = [x for x in assembly.composition.instances if x.name == name]
        assert len(instances) == 1, 'Found registered fill frame with no associated ' \
            'instance (template bug?)'
        instance, = instances
        perspective = Perspective(instance=name, group=instance.address_space)

        elf_name = perspective['elf_name']
        assert elf_name in elfs, 'Failed to find binary image for instance %s' % name
        elf = elfs[elf_name]

        # Find the vspace root
        root_name = perspective['pd']
        roots = [x for x in obj_space.spec.objs if x.name == root_name]
        assert len(roots) == 1, 'No vspace found for instance %s' % name
        root, = roots

        # Go over all the fill symbols
        for symbol,fill in iter(fill_frames[name]):
            base = get_symbol_vaddr(elf, symbol)
            assert base is not None, 'Registered fill symbol not found in elf image (template bug?)'
            # Ensure this symbol is correctly aligned
            assert base % PAGE_SIZE == 0, 'Fill symbol in elf image is not correctly aligned (template bug?)'

            (cap, frame) = frame_for_vaddr(arch, root, base, PAGE_SIZE)
            assert frame is not None, 'Failed to find frame for symbol at %x (CAmkES bug?)' % base
            frame.set_fill(fill)

def replace_dma_frames(ast, obj_space, elfs, options, **_):
    '''Locate the DMA pool (a region that needs to have frames whose mappings
    can be reversed) and replace its backing frames with pre-allocated,
    reversible ones.'''

    if not elfs:
        # If we haven't been passed any ELF files this step is not relevant yet.
        return

    arch = lookup_architecture(options.architecture)
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
            name = p['dma_frame_symbol']
            assert name in obj_space, "No such symbol in capdl spec %s" % name
            return obj_space[name]

        # Ensure paging structures are in place to map in dma frames
        replace_large_frames(obj_space, arch, pd, base, sz, page_size)

        for page_vaddr in six.moves.range(base, base + sz, page_size):
            cap = Cap(get_dma_frame(dma_frame_index), True, True, False)
            cap.set_cached(False)
            update_frame_in_vaddr(arch, pd, page_vaddr, page_size, cap)
            dma_frame_index = dma_frame_index + 1

def guard_cnode_caps(cspaces, options, **_):
    '''If the templates have allocated any caps to CNodes, they will not have
    the correct guards. This is due to the CNodes' sizes being automatically
    calculated (during set_tcb_caps above). Correct them here.'''

    arch = lookup_architecture(options.architecture)
    for space in cspaces.values():
        [cap.set_guard_size(arch.word_size_bits() - cap.referent.size_bits)
            for cap in space.cnode.slots.values()
            if cap is not None and isinstance(cap.referent, CNode)]

def guard_pages(obj_space, cspaces, elfs, options, **_):
    '''Introduce a guard page around each stack and IPC buffer. Note that the
    templates should have ensured a three page region for each stack in order to
    enable this.'''

    arch = lookup_architecture(options.architecture)
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

                (cap, frame) = frame_for_vaddr(arch, pd, pre_guard, PAGE_SIZE)
                if frame is None:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                # Delete the page.
                obj_space.remove(frame)
                update_frame_in_vaddr(arch, pd, pre_guard, PAGE_SIZE, None)

                # Now do the same for the following guard page. We do this
                # calculation separately just in case the region crosses a PT
                # boundary and the two guard pages are in separate PTs.

                post_guard = pre_guard + 2 * PAGE_SIZE

                (cap, frame) = frame_for_vaddr(arch, pd, post_guard, PAGE_SIZE)
                if frame is None:
                    raise Exception('IPC buffer region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                obj_space.remove(frame)
                update_frame_in_vaddr(arch, pd, post_guard, PAGE_SIZE, None)

                # Now we do the same thing for the preceding guard page of the
                # thread's stack...

                stack_symbol = perspective['stack_symbol']

                pre_guard = get_symbol_vaddr(elf, stack_symbol)

                (cap, frame) = frame_for_vaddr(arch, pd, pre_guard, PAGE_SIZE)
                if frame is None:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                obj_space.remove(frame)
                update_frame_in_vaddr(arch, pd, pre_guard, PAGE_SIZE, None)

                # ...and the following guard page.

                stack_region_size = get_symbol_size(elf, stack_symbol)
                assert stack_region_size % PAGE_SIZE == 0, \
                    'stack region is not page-aligned'
                assert stack_region_size >= 3 * PAGE_SIZE, \
                    'stack region has no room for guard pages'
                post_guard = pre_guard + stack_region_size - PAGE_SIZE

                (cap, frame) = frame_for_vaddr(arch, pd, post_guard, PAGE_SIZE)
                if frame is None:
                    raise Exception('stack region of TCB %s in '
                        'group %s does not appear to be backed by a frame'
                        % (tcb.name, group))

                obj_space.remove(frame)
                update_frame_in_vaddr(arch, pd, post_guard, PAGE_SIZE, None)

def tcb_default_properties(obj_space, options, **_):
    '''Set up default thread priorities. Note this filter needs to operate
    *before* tcb_priorities.'''

    for t in [x for x in obj_space if isinstance(x, TCB)]:
        t.prio = options.default_priority
        t.max_prio = options.default_max_priority
        t.affinity = options.default_affinity

def sc_default_properties(obj_space, options, **_):
    '''Set up default scheduling context properties. Note this filter needs to operate
    *before* sc_properties.'''

    for s in (x for x in obj_space if isinstance(x, SC)):
        s.period = options.default_period
        s.budget = options.default_budget
        s.data = options.default_data
        s.size_bits = options.default_size_bits

def maybe_set_property_from_configuration(assembly, perspective, obj, field_name, attribute_name, general_attribute):
    '''Sets a field "field_name" of an object "obj" to the value of a configuration
    setting of the form:
    instance.attribute = value;
    where "instance" and "attribute" are obtained from the perspective argument
    which is queried for the current instance, and the value corresponding to
    attribute_name respectively.
    If such a setting exists, the field is set.
    Otherwise, check if a corresponding general property was set for the instance.
    This is a setting that applies the property to all threads related to the instance
    including all interface threads.'''

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
    ''' Override a TCB's default property if the user has specified this in an
    attribute.'''

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
    ''' Override an SC's default properties if the user has specified this in an
    attribute.'''

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
    '''Set the domain of a TCB if the user has specified this in an
    attribute.'''

    assembly = ast.assembly

    # HACK: For capDL verification, the generator model assumes that
    # each component is assigned to the domains 1, 2, …. We're not sure
    # why it does that, but for now, we replicate that here.
    # See issue VER-945.
    domain_model_ids = None
    if os.environ.get('CONFIG_CAMKES_LABEL_MAPPING', '') == 'y':
        domain_model_ids = dict(
            (comp.name, dom) for dom, comp in
            enumerate(assembly.composition.instances, 1))

    if (domain_model_ids is None and
          (assembly.configuration is None or
           len(assembly.configuration.settings) == 0)):
        # Nothing to do.
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

            # Auto-assign domains if we're doing the capDL verification.
            if dom is None and domain_model_ids is not None:
                if perspective['instance'] in domain_model_ids:
                    dom = domain_model_ids[perspective['instance']]

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
    describe_fill_frames,
    guard_cnode_caps,
    guard_pages,
    tcb_default_properties,
    tcb_properties,
    tcb_domains,
    remove_tcb_caps,
    sc_default_properties,
    sc_properties,
]
