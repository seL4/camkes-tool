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

'''
Cscope for CAmkES. Pass --help for usage instructions.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import argparse, os, pycscope, subprocess, sys

MY_DIR = os.path.abspath(os.path.dirname(__file__))

# Make the CAmkES parser importable.
sys.path.append(os.path.join(MY_DIR, '..'))

from camkes.ast import Assembly, Component, Composition, Configuration, Connection, Instance, Reference, Setting

from camkes.parser.stage0 import CPP, Reader
from camkes.parser.stage1 import Parse1
from camkes.parser.stage2 import Parse2
from camkes.parser.stage3 import Parse3

class Import(object):
    def __init__(self, path):
        self.path = path

class Item(object):
    def __init__(self, start_lineno, start_col, end_lineno, end_col, content):
        self.start_lineno = start_lineno
        self.start_col = start_col
        self.end_lineno = end_lineno
        self.end_col = end_col
        self.content = content

class Bucket(object):
    def __init__(self, source):
        self.pending = []
        self.source = source

    def add(self, item):
        self.pending.append(item)

    def to_cscope(self):
        lines = self.source.split('\n')

        lineno = 1
        col = 1
        line = pycscope.Line(lineno)

        for item in sorted(self.pending):
            while item.start_lineno > lineno:
                interloper = lines[lineno - 1][col - 1:]
                if interloper != '':
                    line += pycscope.NonSymbol(interloper)
                yield line
                lineno += 1
                col = 1
                line = pycscope.Line(lineno)

            if item.start_col > col:
                interloper = lines[lineno - 1][col - 1:item.start_col - 1]
                assert interloper != ''
                line += pycscope.NonSymbol(interloper)
                col += len(interloper)
                assert item.start_col == col

            content = item.content

            # The following logic defines how we map CAmkES entities to the C
            # entities understood by CScope. Note that we map almost everything
            # to function semantics and leave the user to disambiguate.

            if isinstance(content, Assembly):
                assert content.name is not None
                line += pycscope.Symbol(content.name, pycscope.Mark.FUNC_DEF)

            elif isinstance(content, Component):
                assert content.name is not None
                line += pycscope.Symbol(content.name, pycscope.Mark.FUNC_DEF)

            elif isinstance(content, Composition):
                assert content.name is not None
                line += pycscope.Symbol(content.name, pycscope.Mark.FUNC_DEF)

            elif isinstance(content, Configuration):
                assert content.name is not None
                line += pycscope.Symbol(content.name, pycscope.Mark.FUNC_DEF)

            elif isinstance(content, Connection):
                line += pycscope.Symbol(content.name, pycscope.Mark.GLOBAL)

            elif isinstance(content, Import):
                line += pycscope.Symbol(content.path, pycscope.Mark.INCLUDE)

            elif isinstance(content, Instance):
                line += pycscope.Symbol(content.name, pycscope.Mark.GLOBAL)

            elif isinstance(content, Reference):
                line += pycscope.Symbol(content.name, pycscope.Mark.FUNC_CALL)

            elif isinstance(content, Setting):
                line += pycscope.Symbol('%s.%s' % (content.instance,
                    content.attribute), pycscope.Mark.ASSIGN)

def _get_files(dirname):
    assert os.path.isdir(dirname)

    for root, _, files in os.walk(dirname):
        for f in files:
            if os.path.splitext(f)[-1].lower() == '.camkes':
                yield os.path.abspath(os.path.join(root, f))

def get_files(path):
    if os.path.isdir(path):
        for f in _get_files(path):
            yield os.path.split(f[len(os.path.commonprefix([f, path])):])
    else:
        yield os.path.split(path)

def cross_references(path, options):
    index = []

    # Setup a stage 0 parser, to optionally CPP the input.
    if options.cpp:
        s0 = CPP(options.toolprefix, options.cpp_flag)
    else:
        s0 = Reader()

    # Setup a stage 1 parser to translate the source(s) into a plyplus AST.
    s1 = Parse1(s0)

    # Setup a stage 2 parser, though we will not actually utilise its
    # functionality. We'll strip the import statements before going beyond
    # stage 1 to mask any subordinate parse errors.
    s2 = Parse2(s1)

    # Setup a stage 3 parser. This is as far as we will go, and we only go to
    # this point in order to take advantage of the `LiftedAST` representation.
    s3 = Parse3(s2)

    for base, name in get_files(path):
        abspath = os.path.join(base, name)

        # File index entry.
        yield '\n%s%s\n\n' % (pycscope.Mark(pycscope.Mark.FILE),
            abspath), abspath

        _, ast, _ = s1.parse_file(os.path.join(base, name))

        # We want to eventually parse this to a proper AST, but we first need
        # to handle import statements as we don't want to actually import any
        # extra files.

def build_cross_reference(path, options):
    index = []
    files = set()

    for result in cross_references(path, options):

        if isinstance(result, Warning):
            sys.stderr.write('warning: %s\n' % str(result))

        else:
            entry, file = result
            index.append(entry)
            files.add(file)

    return index, list(files)

def main(argv):
    parser = argparse.ArgumentParser(
        description='Cscope for CAmkES specifications')
    parser.add_argument('--cpp', action='store_true', help='Pre-process the '
        'source with CPP')
    parser.add_argument('--nocpp', action='store_false', dest='cpp',
        help='Do not pre-process the source with CPP')
    parser.add_argument('--toolprefix', help='compiler toolchain prefix',
        default='')
    parser.add_argument('--cpp-flag', action='append', default=[],
        help='Specify a flag to pass to CPP')
    parser.add_argument('--import-path', '-I', help='Add this path to the list '
        'of paths to search for built-in imports. That is, add it to the list '
        'of directories that are searched to find the file "foo" when '
        'encountering an expression "import <foo>;".', action='append',
        default=[])
    parser.add_argument('--build-cross-reference-only', '-b',
        action='store_true', help='Build the cross-reference only')
    parser.add_argument('--ignore-case', '-C', action='store_true',
        help='Ignore the letter case when searching')
    parser.add_argument('--no-update', '-d', action='store_true', help='Do '
        'not update the cross-reference')
    parser.add_argument('--reference-file', '-f', type=argparse.FileType('w'),
        help='Use FILE as the cross-reference file name instead of the '
        'default "camkes-scope.out".', default=open('camkes-scope.out', 'wt'))
    parser.add_argument('source', default=os.getcwd(), help='file or '
        'directory to scan', nargs='?')
    opts = parser.parse_args(argv[1:])

    if not os.path.exists(opts.source):
        sys.stderr.write('%s does not exist\n' % opts.source)
        return -1

    # Set up a default import path to help the user out.
    if len(opts.import_path) == 0:
        opts.import_path.append(os.path.join(MY_DIR, '../include/builtin'))

    if not opts.no_update:
        index, files = build_cross_reference(opts.source, opts)

        if os.path.isdir(opts.source):
            target = opts.source
        else:
            target = os.path.dirname(opts.source)
        base = os.path.relpath(target,
            os.path.dirname(opts.reference_file.name))

        pycscope.writeIndex(base, opts.reference_file, index, files)

    if opts.build_cross_reference_only:
        return 0

    args = []
    if opts.ignore_case:
        args.append('-C')

    # Run Cscope.
    return subprocess.call(['cscope', '-d', '-f%s' % opts.reference_file.name] +
        args)

if __name__ == '__main__':
    sys.exit(main(sys.argv))
