#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
CAmkES source linter.

This tool is designed to recognise various Python programming idioms used in
the CAmkES sources and report likely typos in them. It is fairly limited right
now, but feel free to extend it to detect more idioms.
'''

import argparse, ast, codecs, sys

def main(argv):
    parser = argparse.ArgumentParser(
        description='check source files for mistaken CAmkES idioms')
    parser.add_argument('filename', help='file to check',
        type=argparse.FileType('r'))
    options = parser.parse_args(argv[1:])

    # Parse the input as UTF-8 as all the CAmkES sources are intended to be
    # UTF-8-clean.
    with codecs.open(options.filename.name, 'rt', 'utf-8') as f:
        st = ast.parse(f.read().encode('utf-8'))

    result = 0

    # Walk the AST of the input file looking for functions.
    for node in (x for x in ast.walk(st) if isinstance(x, ast.FunctionDef)):

        # Extract the names of the arguments to this function.
        args = [x.id for x in node.args.args]

        # Scan any leading assertions in the function's body.
        for stmt in node.body:
            if not isinstance(stmt, ast.Assert):
                break

            # Extract the body of the assertion.
            test = stmt.test

            # Now try to recognise two idioms:
            #  1. `assert foo is None or isinstance(foo, ...)`; and
            #  2. `assert isinstance(foo, ...)`.
            # These idioms are used in the CAmkES sources to perform runtime
            # type-checking of function parameters. Any deviation from the
            # above templates likely indicates a typo.

            # In the following variable, we'll store the node corresponding to
            # the `isinstance` call in one of the two above idioms.
            insttest = None

            # Try to recognise case (1).
            if isinstance(test, ast.BoolOp) and \
               isinstance(test.op, ast.Or) and \
               isinstance(test.values[0], ast.Compare) and \
               isinstance(test.values[0].left, ast.Name) and \
               len(test.values[0].ops) == 1 and \
               isinstance(test.values[0].ops[0], ast.Is) and \
               len(test.values[0].comparators) == 1 and \
               isinstance(test.values[0].comparators[0], ast.Name):

                if test.values[0].left.id not in args:
                    sys.stderr.write('%s:%d: leading assertion references '
                        '`%s` that is not a function argument\n' %
                        (options.filename.name, test.values[0].left.lineno,
                        test.values[0].left.id))
                    result |= -1

                if test.values[0].comparators[0].id != 'None':
                    sys.stderr.write('%s:%d: leading `is` assertion against '
                        '`%s` instead of `None` as expected\n' %
                        (options.filename.name,
                        test.values[0].comparators[0].lineno,
                        test.values[0].comparators[0].id))
                    result |= -1

                if isinstance(test.values[1], ast.Call) and \
                   test.values[1].func.id == 'isinstance':
                    insttest = test.values[1]

            # Try to recognise case (2).
            if isinstance(test, ast.Call) and \
               isinstance(test.func, ast.Name) and \
               test.func.id == 'isinstance':
                insttest = test

            # Check the `isinstance` contents.
            if insttest is not None:
                if len(insttest.args) != 2:
                    sys.stderr.write('%s:%d: %d arguments to `isinstance` '
                        'instead of 2 as expected\n' % (options.filename.name,
                        insttest.lineno, len(insttest.args)))
                    result |= -1

                elif not isinstance(insttest.args[0], (ast.Name, ast.Attribute)):
                    sys.stderr.write('%s:%d: unexpected first argument to '
                        '`isinstance`\n' % (options.filename.name,
                        insttest.args[0].lineno))
                    result |= -1

                elif isinstance(insttest.args[0], ast.Name) and \
                     insttest.args[0].id not in args:
                    sys.stderr.write('%s:%d: leading assertion references '
                        '`%s` that is not a function argument\n' %
                        (options.filename.name, insttest.args[0].lineno,
                        insttest.args[0].id))
                    result |= -1

                elif isinstance(insttest.args[0], ast.Attribute) and \
                     (not isinstance(insttest.args[0].value, ast.Name) or
                     insttest.args[0].value.id != 'self'):
                    sys.stderr.write('%s:%d: leading assertion references '
                        '`%s.%s` that is not a function argument\n' %
                        (options.filename.name, insttest.args[0].lineno,
                        insttest.args[0].value.id, insttest.args[0].attr))
                    result |= -1

    return result

if __name__ == '__main__':
    sys.exit(main(sys.argv))
