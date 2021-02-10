#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Dependency checker for CAmkES.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

# This script can only import parts of the Python standard library, or it
# becomes useless as a dependency checker.
import abc, argparse, importlib, os, re, shutil, subprocess, sys, tempfile

class CheckDepException(Exception):
    pass

class Package(object):

    # Note that the following line has no effect in Python 3, but we just live
    # with this rather than using the `six` wrapper as that would introduce a
    # dependency on `six` that the user may not have installed.
    __metaclass__ = abc.ABCMeta

    def __init__(self, name, description):
        self.name = name
        self.description = description

    @abc.abstractmethod
    def exists(self):
        raise NotImplementedError

class Binary(Package):
    def exists(self):
        with open(os.devnull, 'wt') as f:
            return subprocess.call(['which', self.name], stdout=f, stderr=f) \
                == 0

class Pylint(Binary):
    def __init__(self, name, description, min_version):
        super(Pylint, self).__init__(name, description)
        self.min_version = min_version

    def exists(self):
        if not super(Pylint, self).exists():
            return False
        with open(os.devnull, 'wt') as f:
            output = subprocess.check_output(['pylint', '--version'], stderr=f)
        m = re.search(r'^pylint\s+(\d+\.\d+)', output, flags=re.MULTILINE)
        if m is None:
            raise CheckDepException('cannot determine version')
        version = float(m.group(1))
        if version < self.min_version:
            raise CheckDepException('found version %0.1f but need at least '
                'version %0.1f' % (version, self.min_version))
        return True

class PythonModule(Package):
    def exists(self):
        try:
            importlib.import_module(self.name)
            return True
        except ImportError:
            return False

class PythonModuleWith(PythonModule):
    def __init__(self, name, description, attr):
        super(PythonModuleWith, self).__init__(name, description)
        self.attr = attr

    def exists(self):
        if not super(PythonModuleWith, self).exists():
            return False
        mod = importlib.import_module(self.name)
        if not hasattr(mod, self.attr):
            raise CheckDepException('module exists, but %s.%s not found '
                '(upgrade required?)' % (self.name, self.attr))
        return True

class CLibrary(Package):
    def exists(self):
        with open(os.devnull, 'wt') as f:
            return subprocess.call(['pkg-config', '--cflags', self.name],
                stdout=f, stderr=f) == 0

class Or(Package):
    def __init__(self, *packages):
        self.name = ' or '.join(p.name for p in packages)
        self.description = '...'
        self.packages = packages

    def exists(self):
        return any(p.exists() for p in self.packages)

class CUnit(Package):
    def exists(self):
        # CUnit is misconfigured for use with `pkg-config`, so test for its
        # existence manually.
        tmp = tempfile.mkdtemp()
        try:
            source = os.path.join(tmp, 'main.c')
            with open(source, 'wt') as f:
                f.write('''
                    #include <CUnit/Basic.h>

                    int main(void) {
                        CU_initialize_registry();
                        CU_cleanup_registry();
                        return 0;
                    }''')
            with open(os.devnull, 'wt') as f:
                subprocess.check_call(['gcc', 'main.c', '-lcunit'], cwd=tmp,
                    stdout=f, stderr=f)
            return True
        except subprocess.CalledProcessError:
            return False
        finally:
            shutil.rmtree(tmp)

def green(string):
    return '\033[32;1m%s\033[0m' % string

def red(string):
    return '\033[31;1m%s\033[0m' % string

def yellow(string):
    return '\033[33m%s\033[0m' % string

DEPENDENCIES = {
    'CAmkES runner':(PythonModule('jinja2', 'Python templating module'),
                     PythonModule('plyplus', 'Python parsing module'),
                     PythonModule('ply', 'Python parsing module'),
                     PythonModule('elftools', 'Python ELF parsing module'),
                     PythonModule('orderedset', 'Python OrderedSet module (orderedset)'),
                     PythonModuleWith('six', 'Python 2/3 compatibility layer', 'assertCountEqual'),
                     PythonModule('sqlite3', 'Python SQLite module'),
                     PythonModule('pyfdt', 'Python flattened device tree parser')),
    'seL4':(Binary('gcc', 'C compiler'),
            PythonModule('tempita', 'Python templating module'),
            Binary('xmllint', 'XML validator'),
            Binary('bash', 'shell'),
            Binary('make', 'GNU Make build tool'),
            Binary('cpio', 'CPIO file system tool')),
    'CapDL translator':(Binary('stack', 'Haskell version manager'),),
    'CAmkES test suite':(Binary('expect', 'automation utility'),
                         Pylint('pylint', 'Python linter', 1.4),
                         Binary('qemu-system-arm', 'ARM emulator'),
                         Binary('qemu-system-i386', 'IA32 emulator'),
                         PythonModule('pycparser', 'Python C parsing module'),
                         Binary('gcc', 'C compiler'),
                         Binary('spin', 'model checker'),
                         Binary('sha256sum', 'file hashing utility')),
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
        Binary('arm-linux-gnueabi-gcc', 'ARM C compiler'),
        Binary('arm-linux-gnu-gcc', 'ARM C compiler')),
        'you will need one of these if you want to target ARM systems'),
    (Binary('pandoc', 'document format translator'),
        'you will need this if you want to build the CAmkES documentation'),
    (Binary('astyle', 'code reformater'),
        'installing this will allow you to use the "style" Makefile targets to reformat C code'),
    (Binary('c-parser', 'NICTA C-to-Simpl parser'),
        'you will need this installed if you want to validate code for verification'),
    (Or(Binary('arm-none-eabi-objdump', 'ARM disassembler'),
        Binary('arm-linux-gnueabi-objdump', 'ARM disassembler'),
        Binary('arm-linux-gnu-objdump', 'ARM disassembler')),
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
    (Binary('figleaf', 'code coverage tool for Python'),
        'you will need this installed if you want to measure code coverage within CAmkES'),
    (Binary('python-coverage', 'code coverage tool for Python'),
        'you will need this installed if you want to measure code coverage within CAmkES'),
    (Binary('clang', 'C compiler'),
        'you will need this installed to efficiently use large DMA pools on ARM'),

))

def main(argv):
    parser = argparse.ArgumentParser(description='CAmkES dependency checker')
    parser.add_argument('--component', '-c', action='append',
        choices=list(DEPENDENCIES.keys()), help='component whose dependecies '
        'should be checked (default: all)')
    options = parser.parse_args(argv[1:])

    ret = 0

    for k, v in sorted(DEPENDENCIES.items()):
        if options.component is not None and k not in options.component:
            continue
        ok = True
        sys.stdout.write('Dependencies of %s\n' % k)
        for p in v:
            sys.stdout.write(' %s (%s)... ' % (p.name, p.description))
            try:
                if p.exists():
                    sys.stdout.write(green('Found\n'))
                else:
                    raise CheckDepException('Not found')
            except CheckDepException as e:
                ok = False
                ret = -1
                sys.stdout.write(red('%s\n' % e))
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
