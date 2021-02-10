#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Run pylint on a Jinja 2 template.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import atexit, jinja2, os, shutil, subprocess, sys, tempfile

# Clagged pieces from the runner.
START_BLOCK = '/*-'
END_BLOCK = '-*/'
START_VARIABLE = '/*?'
END_VARIABLE = '?*/'
START_COMMENT = '/*#'
END_COMMENT = '#*/'

def main(argv, out, err):
    if len(argv) < 2 or argv[1] in ['--help', '-?']:
        err.write('%s file pylint_args...\n' % argv[0])
        return -1

    if not os.path.exists(argv[1]):
        err.write('%s not found\n' % argv[1])
        return -1

    root, template = os.path.split(os.path.abspath(argv[1]))

    # Construct a Jinja environment that matches that of the runner.
    env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(root),
        extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
        block_start_string=START_BLOCK,
        block_end_string=END_BLOCK,
        variable_start_string=START_VARIABLE,
        variable_end_string=END_VARIABLE,
        comment_start_string=START_COMMENT,
        comment_end_string=END_COMMENT)

    # Compile the template requested to a temporary directory.
    tmp = tempfile.mkdtemp()
    atexit.register(shutil.rmtree, tmp)
    out.write('compiling to %s...\n' % tmp)
    env.compile_templates(tmp, filter_func=lambda x: x == template, zip=None,
        ignore_errors=False)

    # Find it and run pylint on it.
    py = os.path.join(tmp, os.listdir(tmp)[0])
    out.write('running pylint on %s...\n' % py)
    return subprocess.call(['pylint', py] + argv[2:])

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
