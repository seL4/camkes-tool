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
Tests related to preventing regression of previously existing bugs.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, subprocess, sys, unittest

ME = os.path.abspath(__file__)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest

class TestRegression(CAmkESTest):
    def test_camkes439(self):
        '''
        Test that the level B cache correctly notes changes to custom
        templates.
        '''

        cachedir = self.mkdtemp()

        templates = self.mkdtemp()
        with open(os.path.join(templates, 'foo'), 'wt') as f:
            f.write('foo\n')

        spec = '''
            connector Foo {
                from Event template "foo";
                to Event;
            }

            component A {
                emits Ev e;
            }

            component B {
                consumes Ev e;
            }

            assembly {
                composition {
                    component A a;
                    component B b;

                    connection Foo f(from a.e, to b.e);
                }
            }
            '''
        specdir = self.mkdtemp()
        with open(os.path.join(specdir, 'spec'), 'wt') as f:
            f.write(spec)

        camkessh = os.path.join(os.path.dirname(ME), '../../../camkes.sh')

        # Rely on the location of the CapDL module.
        pythoncapdl = os.path.join(os.path.dirname(ME),
            '../../../../python-capdl')
        env = os.environ.copy()
        if 'PYTHONPATH' in env:
            pythonpath = '%s:' % env['PYTHONPATH']
        else:
            pythonpath = ''
        env['PYTHONPATH'] = '%s%s' % (pythonpath, pythoncapdl)

        builtins = os.path.join(os.path.dirname(ME), '../../../include/builtin')

        outdir = self.mkdtemp()

        # Run the code generator once.
        subprocess.check_call([camkessh, '--cache', '--cache-dir', cachedir,
            '--import-path', builtins, '--templates', templates,
            '--architecture', 'aarch32', '--file', os.path.join(specdir, 'spec'),
            '--item', 'f/from/source/0', '--outfile',
            os.path.join(outdir, 'out1'), '--platform', 'seL4'], env=env)

        # Confirm that we got what we expected from the output.
        with open(os.path.join(outdir, 'out1')) as f:
            content = f.read()
        self.assertEqual(content, 'foo')

        # Now edit the template.
        with open(os.path.join(templates, 'foo'), 'wt') as f:
            f.write('bar\n')

        # Re-run the code generator.
        subprocess.check_call([camkessh, '--cache', '--cache-dir', cachedir,
            '--import-path', builtins, '--templates', templates,
            '--architecture', 'aarch32', '--file', os.path.join(specdir, 'spec'),
            '--item', 'f/from/source/0', '--outfile',
            os.path.join(outdir, 'out2'), '--platform', 'seL4'], env=env)

        # Confirm that the change to the template was noticed.
        with open(os.path.join(outdir, 'out2')) as f:
            content = f.read()
        self.assertEqual(content, 'bar')

if __name__ == '__main__':
    unittest.main()
