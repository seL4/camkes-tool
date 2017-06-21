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
Simple compiler wrapper that falls back on calling Clang when GCC fails.

Background: For mysterious reasons, ARM GCC toolchains limit the maximum
alignment constraint on variables in custom sections to `1 << 15`. To quote the
relevant GAS sources at time of writing:

   gas/config/tc-arm.c:2980 @ f0b0791b05ed335e5d74d843d828645805db1f9c:

       long max_alignment = 15;

Clang has no such constraint. To try and deal with this situation in the seL4
build system, we provide this wrapper. Its intent is to detect when GCC fails
due to this unnecessary alignment restriction and, instead of failing outright,
call Clang to build the same source file.

----

Update: this limitation was removed by Alan Modra (amodra@gmail.com) on
2015-08-17. Once this updated binutils has sufficiently propagated, this
wrapper can be removed. For more information:

    https://www.sourceware.org/ml/binutils/2015-08/msg00119.html
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, subprocess, sys

def main(argv):
    toolprefix = os.environ.get('TOOLPREFIX', '')
    p = subprocess.Popen(['%sgcc' % toolprefix] + argv[1:],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    stdout, stderr = p.communicate()
    sys.stdout.write(stdout)
    sys.stderr.write(stderr)
    ret = p.returncode

    if ret != 0 and re.search(r'Error: alignment too large: \d+ assumed',
            stderr) is not None:
        sys.stderr.write('Attempting to work around alignment constraint '
            'with Clang...\n')
        clang = ['clang', '-integrated-as']
        if toolprefix == 'arm-none-eabi-':
            clang.extend(('-target', 'arm-none-eabi'))
        elif toolprefix == 'arm-linux-gnueabi-':
            clang.extend(('-target', 'arm-linux-gnueabi'))
        ret = subprocess.call(clang + argv[1:])

    return ret

if __name__ == '__main__':
    sys.exit(main(sys.argv))
