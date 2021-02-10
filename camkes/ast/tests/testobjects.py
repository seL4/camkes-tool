#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import inspect, os, sys, unittest

ME = os.path.abspath(__file__)

# Make camkes.ast importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.ast.base import *
from camkes.ast.liftedast import *
from camkes.ast.objects import ASTObject
from camkes.ast.objects import *
from camkes.internal.tests.utils import CAmkESTest

class TestObjects(CAmkESTest):
    def test_child_fields(self):
        '''
        Test all the AST objects have valid `child_fields` class members.

        We do this in a seemingly hacky way by dynamically discovering the AST
        objects through the `globals` dictionary in order to ensure we notice
        new AST object classes, even if developers forget to tell us about
        them.

        This test may seem to be checking something obvious, but it is very
        easy to write `child_fields = ('hello')` and think you defined a tuple
        when you really just defined a string.
        '''
        for c in globals().values():
            if inspect.isclass(c) and issubclass(c, ASTObject):
                self.assertTrue(hasattr(c, 'child_fields'),
                    '%s has no child_fields class member' % c.__name__)
                self.assertIsInstance(c.child_fields, tuple, '%s\'s '
                    'child_field member is not a tuple as expected' %
                    c.__name__)
                seen = set()
                for f in c.child_fields:
                    self.assertNotIn(f, seen,
                        'duplicate child field %s in %s' % (f, c.__name__))
                    seen.add(f)

    def test_no_hash(self):
        '''
        Test all AST objects have a well-formed `no_hash` class member.

        `ASTObject`, and all its descendents, should have a `no_hash` class
        member that defines fields that should not be considered when doing
        object hashes or comparisons. Importantly, children should never
        remove `no_hash` members that their parents' defined. This test ensures
        that every child of `ASTObject` has all the `no_hash` objects of its
        parents.
        '''
        for c in globals().values():
            if inspect.isclass(c) and issubclass(c, ASTObject):
                # For each parent class between `c` and `ASTObject` inclusively
                for parent in [p for p in c.__bases__
                        if issubclass(p, ASTObject)]:
                    self.assertLessEqual(set(parent.no_hash), set(c.no_hash),
                        '%s discards no_hash members from its parent %s' %
                        (c.__name__, parent.__name__))

    def test_freezing_monotonic(self):
        '''
        We should not be able to unfreeze (thaw) an AST object.
        '''
        p = Procedure()
        p.freeze()
        with self.assertRaises(TypeError):
            p.frozen = False

if __name__ == '__main__':
    unittest.main()
