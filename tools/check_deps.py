#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Dependency checker for CAmkES.
'''

# This script can only import parts of the Python standard library, or it
# becomes useless as a dependency checker.
import abc, argparse, importlib, os, shutil, subprocess, sys, tempfile

class CheckDepException(Exception):
    pass

class Package(object):
    __metaclass__ = abc.ABCMeta

    def __init__(self, name, description):
        self.name = name
        self.description = description

    @abc.abstractmethod
    def exists(self):
        '''
        Whether this package is available.
        '''
        raise NotImplementedError

class Binary(Package):
    def exists(self):
        with open(os.devnull, 'w') as f:
            return subprocess.call(['which', self.name], stdout=f, stderr=f) \
                == 0

class PythonModule(Package):
    def exists(self):
        try:
            importlib.import_module(self.name)
            return True
        except ImportError:
            return False

class CLibrary(Package):
    def exists(self):
        with open(os.devnull, 'w') as f:
            return subprocess.call(['pkg-config', '--cflags', self.name],
                stdout=f, stderr=f) == 0

class HaskellModule(Package):
    def __init__(self, name, description, import_target):
        super(HaskellModule, self).__init__(name, description)
        self.import_target = import_target

    def exists(self):
        # If only GHCI would exit with non-zero on error, the below shenanigans
        # would not be necessary.
        tmp = tempfile.mkdtemp()
        try:
            source = os.path.join(tmp, 'Main.hs')
            with open(source, 'w') as f:
                f.write('import %s\nmain = return 0' % self.import_target)
            with open(os.devnull, 'w') as f:
                return subprocess.call(['ghc', 'Main.hs'], cwd=tmp, stdout=f,
                    stderr=f) == 0
        finally:
            shutil.rmtree(tmp)

class Or(Package):
    def __init__(self, *packages):
        self.name = ' or '.join(p.name for p in packages)
        self.description = '...'
        self.packages = packages

    def exists(self):
        return any(p.exists() for p in self.packages)

def green(string):
    return '\033[32;1m%s\033[0m' % string

def red(string):
    return '\033[31;1m%s\033[0m' % string

def yellow(string):
    return '\033[33m%s\033[0m' % string

DEPENDENCIES = {
    'CAmkES runner':(PythonModule('jinja2', 'Python templating module'),
                     PythonModule('ply', 'Python parsing module'),
                     PythonModule('elftools', 'Python ELF parsing module')),
    'seL4':(Binary('gcc', 'C compiler'),
            PythonModule('tempita', 'Python templating module'),
            Binary('xmllint', 'XML validator'),
            Binary('bash', 'shell'),
            Binary('make', 'GNU Make build tool'),
            Binary('cpio', 'CPIO file system tool')),
    'CapDL translator':(Binary('ghc', 'Haskell compiler'),
                        HaskellModule('parsec', 'Haskell parsing module', 'Text.ParserCombinators.Parsec'),
                        HaskellModule('mtl', 'Haskell monad transformers module', 'Control.Monad.State'),
                        HaskellModule('containers', 'Haskell containers module', 'Data.Set'),
                        HaskellModule('MissingH', 'Haskell extras module', 'Data.String.Utils'),
                        HaskellModule('split', 'Haskell split utilities', 'Data.List.Split'),
                        HaskellModule('array', 'Haskell arrays module', 'Data.Array.IO'),
                        HaskellModule('pretty', 'Haskell pretty printing module', 'Text.PrettyPrint'),
                        HaskellModule('filepath', 'Haskell file paths module', 'System.FilePath.Posix'),
                        Binary('cabal', 'Haskell package manager')),
    'CAmkES test suite':(Binary('expect', 'automation utility'),
                         Binary('pylint', 'Python linter'),
                         Binary('qemu-system-arm', 'ARM emulator'),
                         Binary('qemu-system-i386', 'IA32 emulator')),
}

EXTRAS = frozenset((
    (Binary('sponge', 'input coalescer from moreutils'),
        'installing this will give a marginal improvement in compilation times'),
    (Binary('qemu-system-arm', 'ARM emulator'),
        'this is required to simulate ARM systems'),
    (Binary('qemu-system-i386', 'IA32 emulator'),
        'this is required to simulate IA32 systems'),
    (Binary('ccache', 'C compiler accelerator'),
        'installing this will speed up your C compilation times'),
    (Binary('clang-format', 'Clang code reformatter'),
        'installing this will reflow generated C code to make it more readable'),
    (CLibrary('ncurses', 'terminal menus library'),
        'you will need to install this if you want to run menuconfig'),
    (Or(Binary('arm-none-eabi-gcc', 'ARM C compiler'),
        Binary('arm-linux-gnueabi-gcc', 'ARM C compiler')),
        'you will need one of these if you want to target ARM systems'),
    (Binary('pandoc', 'document format translator'),
        'you will need this if you want to build the CAmkES documentation'),
    (Binary('astyle', 'code reformater'),
        'installing this will allow you to use the "style" Makefile targets to reformat C code'),
    (Binary('c-parser', 'NICTA C-to-Simpl parser'),
        'you will need this installed if you want to validate code for verification'),
    (Or(Binary('arm-none-eabi-objdump', 'ARM disassembler'),
        Binary('arm-linux-gnueabi-objdump', 'ARM disassembler')),
        'installing one of these will speed up CapDL generation times for ARM builds'),
    (Binary('objdump', 'disassembler'),
        'installing this will speed up CapDL generation times for IA32 builds'),
    (Binary('VBoxManage', 'VirtualBox administration tool'),
        'you will need this installed if you want to build VMWare images'),
    (Binary('syslinux', 'Linux bootloader tool'),
        'you will need this installed if you want to build QEMU images for IA32'),
    (Binary('mpartition', 'partitioning tool for MSDOS disks'),
        'you will need this installed if you want to build QEMU images for IA32'),
    (Binary('mformat', 'formatting tool for MSDOS disks'),
        'you will need this installed if you want to build QEMU images for IA32'),
    (Binary('mcopy', 'copying tool for MSDOS disks'),
        'you will need this installed if you want to build QEMU images for IA32'),
))

def main(argv):
    parser = argparse.ArgumentParser(description='CAmkES dependency checker')
    parser.add_argument('--component', '-c', action='append',
        choices=DEPENDENCIES.keys(), help='component whose dependencies should '
            'be checked (default: all)')
    options = parser.parse_args(argv[1:])

    ret = 0

    for k, v in sorted(DEPENDENCIES.items()):
        if options.component is not None and k not in options.component:
            continue
        ok = True
        sys.stdout.write('Dependencies of %s\n' % k)
        for p in v:
            sys.stdout.write(' %s (%s)... ' % (p.name, p.description))
            if p.exists():
                sys.stdout.write(green('Found\n'))
            else:
                ok = False
                ret = -1
                sys.stdout.write(red('Not found\n'))
        if not ok:
            sys.stdout.write(red('You will not be able to build/run this component\n'))
        sys.stdout.write('\n')

    printed_header = False
    for p, note in EXTRAS:
        if not p.exists():
            if not printed_header:
                sys.stdout.write('Suggestions:\n')
                printed_header = True
            sys.stdout.write(yellow(' %s (%s): %s\n' % (p.name, p.description, note)))

    return ret

if __name__ == '__main__':
    sys.exit(main(sys.argv))
