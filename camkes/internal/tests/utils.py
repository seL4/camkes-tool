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

import collections, os, shutil, subprocess, tempfile, unittest

def which(command):
    with open(os.devnull, 'wt') as f:
        try:
            return subprocess.check_output(['which', command], stderr=f,
                universal_newlines=True).strip()
        except subprocess.CalledProcessError:
            return None

_cpp_available = None
def cpp_available():
    global _cpp_available
    if _cpp_available is None:
        _cpp_available = which('cpp')
    return _cpp_available

_spin_available = None
def spin_available():
    global _spin_available
    if _spin_available is None:
        _spin_available = which('spin')
    return _spin_available

_plyplus_introspectible = None
def plyplus_introspectible():
    '''
    Returns True if plyplus' internals look like we expect.

    This is irrelevant except for tests that need to reach into plyplus and
    poke at its beating heart. If this function returns False, your only option
    to re-enable tests that depend on it is to inspect the plyplus sources and
    figure out what needs to be updated on our side.
    '''
    global _plyplus_introspectible
    if _plyplus_introspectible is None:
        try:
            from plyplus.grammar_parser import parse
            _plyplus_introspectible = True
        except ImportError:
            _plyplus_introspectible = False
    return _plyplus_introspectible

_c_compiler = None
def c_compiler():
    '''
    Find a C compiler or return `None` if we don't have one.
    '''
    global _c_compiler
    if _c_compiler is None:
        for cc in ('ccomp', # CompCert
                   'gcc', # GCC
                   'clang', # Clang
                   ):
            _c_compiler = which(cc)
            if _c_compiler is not None:
                break
    return _c_compiler

_python_available = None
def python_available():
    '''
    Test whether we can call out to the Python binary.
    '''
    global _python_available
    if _python_available is None:
        _python_available = which('python')
    return _python_available

_sha256sum_available = None
def sha256sum_available():
    '''
    Test whether we can call out to sha256sum.
    '''
    global _sha256sum_available
    if _sha256sum_available is None:
        _sha256sum_available = which('sha256sum')
    return _sha256sum_available

class CAmkESTest(unittest.TestCase):
    '''
    A `unittest` test case with a few more bells and whistles.
    '''
    def setUp(self):
        self.tempdirs = []
        self.tempfiles = []

    def mkdtemp(self):
        tmp = tempfile.mkdtemp()
        self.tempdirs.append(tmp)
        return tmp

    def mkstemp(self):
        _, tmp = tempfile.mkstemp()
        self.tempfiles.append(tmp)
        return tmp

    def execute(self, argv, cwd=os.getcwd(), env=os.environ):
        p = subprocess.Popen(argv, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, cwd=cwd, env=env, universal_newlines=True)
        stdout, stderr = p.communicate()
        return p.returncode, stdout, stderr

    def tearDown(self):
        [shutil.rmtree(t) for t in self.tempdirs]
        [os.remove(t) for t in self.tempfiles]

    def assertLen(self, container, *args):
        '''
        Assert the length of a variable.

        I find this is a common operation I want to do in the CAmkES test suite
        but there seems to be no `unittest` builtin for it.
        '''
        assert isinstance(container, collections.Iterable)
        return self.assertEqual(len(container), *args)
