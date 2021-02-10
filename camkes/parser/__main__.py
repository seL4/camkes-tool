#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''Entry point for the parser.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

from camkes.ast import ASTError
import camkes.internal.log as log

import argparse, functools, locale, numbers, os, re, \
    six, string, sys, traceback, pickle

from camkes.parser import parse_file, ParseError, parse_query_parser_args, print_query_parser_help


def die(options, message):

    if isinstance(message, (list, tuple)):
        for line in message:
            log.error(line)
    else:
        log.error(message)

    tb = traceback.format_exc()
    log.debug('\n --- Python traceback ---\n%s ------------------------\n' % tb)
    sys.exit(-1)

def parse_args(argv, out, err):
    parser = argparse.ArgumentParser(prog='python -m camkes.parser',
        description='parse AST based on a CAmkES specification')
    parser.add_argument('--cpp', action='store_true',
        help='Pre-process the source with CPP.', default=True)
    parser.add_argument('--nocpp', action='store_false', dest='cpp',
        help='Do not pre-process the source with CPP.')
    parser.add_argument('--cpp-bin', default='cpp',
        help='CPP binary to use.')
    parser.add_argument('--cpp-flag', action='append', default=[],
        help='Specify a flag to pass to CPP.')
    parser.add_argument('--import-path', '-I', help='Add this path to the list '
        'of paths to search for built-in imports. That is, add it to the list '
        'of directories that are searched to find the file "foo" when '
        'encountering an expression "import <foo>;".', action='append',
        default=[])
    parser.add_argument('--quiet', '-q', help='No diagnostics.', dest='verbosity',
        default=1, action='store_const', const=0)
    parser.add_argument('--verbose', '-v', help='Verbose diagnostics.',
        dest='verbosity', action='store_const', const=2)
    parser.add_argument('--debug', '-D', help='Extra verbose diagnostics.',
        dest='verbosity', action='store_const', const=3)
    parser.add_argument('--makefile-dependencies', '-MD',
        type=argparse.FileType('w'), help='Write Makefile dependency rule to '
        'FILE')
    parser.add_argument('--allow-forward-references', action='store_true',
        help='Allow referring to objects in your specification that are '
        'defined after the point at which they are referenced.')
    parser.add_argument('--disallow-forward-references', action='store_false',
        dest='allow_forward_references', help='Only permit references in '
        'specifications to objects that have been defined before that point.')

    parser.add_argument('--save-ast', type=argparse.FileType('wb'),
        help='Cache the AST for the specification to this file.', required=True)
    parser.add_argument('--file', '-f', type=argparse.FileType('r'),
        help='Load specification from this file.', required=True)

    options, argv = parser.parse_known_args(argv[1:])
    queries, argv = parse_query_parser_args(argv)

    if argv:
        print("Unparsed arguments present:\n{0}".format(argv))
        parser.print_help()
        print_query_parser_help()
        exit(1)

    options.queries = queries
    return options


def main(argv, out, err):

    options = parse_args(argv, out, err)

    log.set_verbosity(options.verbosity)

    try:
        filename = os.path.abspath(options.file.name)
        ast, read = parse_file(filename, options)

    except (ASTError, ParseError) as e:
        die(options, e.args)


    if options.makefile_dependencies is not None:
        options.makefile_dependencies.write('%s: \\\n  %s\n' %
            (options.save_ast.name, ' \\\n  '.join(sorted(read))))
    pickle.dump(ast, options.save_ast)
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
