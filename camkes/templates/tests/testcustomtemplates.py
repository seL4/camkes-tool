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
This file contains unit test cases related to loading custom templates.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys, unittest

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CapDL importable. Note that we just assume where it is in relation to
# our own directory.
sys.path.append(os.path.join(os.path.dirname(ME), '../../../../python-capdl'))

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.ast import Connection, Connector
from camkes.internal.tests.utils import CAmkESTest
from camkes.templates import TemplateError, Templates

class TestCustomTemplates(CAmkESTest):
    def test_inclusion(self):
        '''
        Test whether we can add a template that includes another template.
        '''

        # Setup some custom templates.
        tmp = self.mkdtemp()
        with open(os.path.join(tmp, 'parent'), 'wt') as f:
            f.write('/*- include "child" -*/\n')
        with open(os.path.join(tmp, 'child'), 'wt') as f:
            f.write('/* nothing */\n')

        # Create template store and add a custom path.
        templates = Templates('seL4')
        templates.add_root(tmp)

        # Invent a fake connector and connection. This is necessary for adding
        # the template.
        c = Connector('foo', 'Event', 'Event', from_template='parent')
        c1 = Connection(c, 'bar', [], [])

        # Add the custom template.
        included = templates.add(c, c1)

        # Now we should have noted the included files.
        self.assertSetEqual(
            set([os.path.join(tmp, 'child'), os.path.join(tmp, 'parent')]),
            included)

    def test_self_inclusion(self):
        '''
        Test that a template that includes itself triggers an exception.
        '''

        # Setup some custom templates.
        tmp = self.mkdtemp()
        with open(os.path.join(tmp, 'parent'), 'wt') as f:
            f.write('/*- include "parent" -*/\n')

        # Create template store and add a custom path.
        templates = Templates('seL4')
        templates.add_root(tmp)

        # Invent a fake connector and connection. This is necessary for adding
        # the template.
        c = Connector('foo', 'Event', 'Event', from_template='parent')
        c1 = Connection(c, 'bar', [], [])

        # Add the custom template.
        with self.assertRaises(TemplateError):
            templates.add(c, c1)

    def test_double_inclusion(self):
        '''
        We should be able to include the same template twice without triggering
        an exception.
        '''

        # Setup some custom templates.
        tmp = self.mkdtemp()
        with open(os.path.join(tmp, 'parent'), 'wt') as f:
            f.write('/*- include "child" -*/\n'
                    '/*- include "child" -*/\n')
        with open(os.path.join(tmp, 'child'), 'wt') as f:
            f.write('/* nothing */\n')

        # Create template store and add a custom path.
        templates = Templates('seL4')
        templates.add_root(tmp)

        # Invent a fake connector and connection. This is necessary for adding
        # the template.
        c = Connector('foo', 'Event', 'Event', from_template='parent')
        c1 = Connection(c, 'bar', [], [])

        # Add the custom template.
        templates.add(c, c1)

    def test_mutual_recursion(self):
        '''
        We should trigger an exception when including ourselves, even when it
        is via an intermediary.
        '''

        # Setup some custom templates.
        tmp = self.mkdtemp()
        with open(os.path.join(tmp, 'greatgrandparent'), 'wt') as f:
            f.write('/*- include "grandparent" -*/\n')
        with open(os.path.join(tmp, 'grandparent'), 'wt') as f:
            f.write('/*- include "parent" -*/\n')
        with open(os.path.join(tmp, 'parent'), 'wt') as f:
            f.write('/*- include "child" -*/\n')
        with open(os.path.join(tmp, 'child'), 'wt') as f:
            f.write('/*- include "greatgrandparent" -*/\n')

        # Create template store and add a custom path.
        templates = Templates('seL4')
        templates.add_root(tmp)

        # Invent a fake connector and connection. This is necessary for adding
        # the template.
        c = Connector('foo', 'Event', 'Event', from_template='greatgrandparent')
        c1 = Connection(c, 'bar', [], [])

        # Add the custom template.
        with self.assertRaises(TemplateError):
            templates.add(c, c1)

if __name__ == '__main__':
    unittest.main()
