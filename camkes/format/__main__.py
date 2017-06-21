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

from __future__ import absolute_import, division, print_function, \
    unicode_literals
from camkes.internal.seven import cmp, filter, map, zip

from camkes.ast import ASTError
from camkes.format import to_xml
from camkes.parser import parse_file, ParseError
import argparse, sys

def main(argv):
    parser = argparse.ArgumentParser(prog='python -m camkes.format',
        description='translate CAmkES specifications')
    parser.add_argument('--file', '-f', help='input file',
        type=argparse.FileType('r'), required=True)
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
    parser.add_argument('--allow-forward-references', action='store_true',
        help='allow refering to objects in your specification that are '
        'defined after the point at which they are referenced')
    parser.add_argument('--disallow-forward-references', action='store_false',
        dest='allow_forward_references', help='only permit references in '
        'specifications to objects that have been defined before that point')
    options = parser.parse_args(argv[1:])

    try:
        ast, _ = parse_file(options.file.name, options)
    except (ASTError, ParseError) as e:
        sys.stderr.write('failed: %s\n' % str(e))
        return -1

    options.outfile.write(to_xml(ast))

    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))
