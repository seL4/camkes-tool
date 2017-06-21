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
A Goanna wrapper to aid in suppressing false positives.

The Goanna static analysis tool is an excellent way of finding bugs in C code,
but it has no systematic way of suppressing false positives in the command line
tool. This wrapper script provides support for C code annotations to suppress
particular classes of warnings in order to achieve this. The C code annotations
are expected to be formulated as multiline-style comments containing
"goanna: suppress=" followed by a comma-separated list of warnings you want to
suppress for that line. For example, if goannacc emitted the following
warnings:

    foo.c:10: warning: Goanna [ARR-inv-index] Severity-High, ...
    foo.c:10: warning: Goanna [MEM-leak-alias] Severity-Medium, ...

and you had examined your source code and confirmed that these are false
positives, you could suppress them with the following comment on line 10:

    return a[x]; /* goanna: suppress=ARR-inv-index,MEM-leak-alias */
'''

import re, subprocess, sys

def execute(args, stdout):
    p = subprocess.Popen(args, stdout=stdout, stderr=subprocess.PIPE,
        universal_newlines=True)
    _, stderr = p.communicate()
    return p.returncode, stderr

def main(argv, out, err):

    # Run Goanna.
    try:
        ret, stderr = execute(['goannacc'] + argv[1:], out)
    except OSError:
        err.write('goannacc not found\n')
        return -1

    if ret != 0:
        # Compilation failed. Don't bother trying to suppress warnings.
        err.write(stderr)
        return ret

    # A regex that matches lines of output from Goanna that represent warnings.
    # See section 10.7 of the Goanna user guide.
    warning_line = re.compile(r'(?P<relfile>[^\s]+):(?P<lineno>\d+):'
        r'\s*warning:\s*Goanna\[(?P<checkname>[^\]]+)\]\s*Severity-'
        r'(?P<severity>\w+),\s*(?P<message>[^\.]*)\.\s*(?P<rules>.*)$')

    # A special formatted comment, instructing us to suppress certain warnings.
    suppression_mark = re.compile(
        r'/\*\s*goanna:\s*suppress\s*=\s*(?P<checks>.*?)\s*\*/')

    for line in stderr.split('\n')[:-1]:

        m = warning_line.match(line)

        if m is not None:
            # This line is a warning.

            relfile = m.group('relfile')
            lineno = int(m.group('lineno'))
            checkname = m.group('checkname')

            # Find the source line that triggered this warning.
            # XXX: Given we may be repeatedly opening and searching the same
            # file, it might make sense to retain open file handles in a cache,
            # but for now just close each file after dealing with the current
            # line.
            source_line = None
            try:
                with open(relfile, 'rt') as f:
                    for index, l in enumerate(f):
                        if index + 1 == lineno:
                            source_line = l
                            break
            except IOError:
                # Source file not found.
                pass

            if source_line is not None:

                # Extract the (possible) suppression marker from this line.
                s = suppression_mark.search(source_line)
                if s is not None:
                    # This line contains a suppression marker.
                    checks = s.group('checks').split(',')
                    if checkname in checks:
                        # The marker matches this warning; suppress.
                        continue

        # If we reached here, either the output line was not a warning, the
        # source file was not found, the line number was invalid or there was no
        # matching suppression marker. Therefore, don't suppress.
        err.write('%s\n' % line)

    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
