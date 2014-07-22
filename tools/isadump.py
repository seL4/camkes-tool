#!/usr/bin/env python
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
This is a tool for extracting the contents of an ELF file into an Isabelle
theory. A concrete map is avoided currently because this doesn't scale, but it
turns out, neither do axioms that enumerate the entire address space. Needs
some work.
'''

import argparse, os, re, struct, sys
from elftools.elf.elffile import ELFFile

THY = '''
theory %(file)s imports
  "../../arm_confidentiality/arm_model"
begin

consts %(file)s :: "(word32, word8) map"

%(axioms)s

end
'''

def main():
    parser = argparse.ArgumentParser(
        description='parse an ELF file into an Isabelle theory')
    parser.add_argument('elf', type=argparse.FileType('r'),
        help='ELF file to read')
    parser.add_argument('--output', '-o',
        help='Output theory', type=argparse.FileType('w'))
    opts = parser.parse_args()

    elf = ELFFile(opts.elf)
    if opts.output is not None:
        name = re.sub(r'\.thy$', '', opts.output.name)
    else:
        name = re.sub(r'[^A-Za-z0-9]', '', os.path.basename(opts.elf.name))
        opts.output = sys.stdout

    axioms = ''

    # Extract mappings from each virtual address to byte.
    addrs = []
    for seg in elf.iter_segments():
        if not seg['p_type'] == 'PT_LOAD':
            continue
        if seg['p_memsz'] == 0:
            continue
        base = int(seg['p_vaddr'])
        data = seg.data()
        for offset in range(int(seg['p_memsz'])):
            if len(data) > offset:
                value = struct.unpack('B', data[offset])[0]
            else:
                value = 0
            addrs.append('%(file)s\'byte\'%(addr)0.8x:"%(file)s 0x%(addr)0.8x = Some 0x%(value)0.2x"' % {
                'file':name,
                'addr':base + offset,
                'value':value,
            })
    axioms += 'axiomatization where\n    %s\n\n' % '\nand '.join(addrs)

    # Extract each symbol and produce a collection of axioms to cover their
    # bytes.
    symtab = elf.get_section_by_name('.symtab')
    if symtab is not None:
        syms = []
        for sym in symtab.iter_symbols():
            base = int(sym['st_value'])
            size = int(sym['st_size'])
            bs = []
            for offset in range(size):
                bs.append('%(file)s\'byte\'%(addr)0.8x' % {
                    'file':name,
                    'addr':base + offset,
                })
            syms.append('lemmas %(file)s\'%(symbol)s = %(bytes)s' % {
                'file':name,
                'symbol':sym.name,
                'bytes':' '.join(bs),
            })
        axioms += '\n\n%s' % '\n\n'.join(syms)

    print >>opts.output, THY % {
        'file':name,
        'axioms':axioms,
    }

    return 0

if __name__ == '__main__':
    sys.exit(main())
