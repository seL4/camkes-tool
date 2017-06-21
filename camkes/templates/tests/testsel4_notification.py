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
This file contains unit test cases related to the seL4Notification connector.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, re, shutil, six, subprocess, sys, unittest
from pycparser import c_ast, c_generator, c_parser

ME = os.path.abspath(__file__)
MY_DIR = os.path.dirname(ME)

# Make CAmkES importable
sys.path.append(os.path.join(os.path.dirname(ME), '../../..'))

from camkes.internal.tests.utils import CAmkESTest

class TestSel4Notification(CAmkESTest):
    def test_locking_protocol(self):
        '''
        The seL4Notification connector uses a binary semaphore internally to protect
        accesses to callback registration. Any functions contained on the "to"
        side, if they acquire this semaphore, are expected to release it before
        exiting. In an early draft of the connector code, there was a single
        execution path where we failed to release the semaphore. This test case
        validates that we always release the semaphore when appropriate, and
        never release it without having first acquired it.

        Note that the static analysis performed in this test case is highly
        simplified and specialised for this connector code. It makes many
        assumptions about code idioms and over approximations of the control
        flow. If you are modifying the seL4Notification connector code in any
        non-trivial way, do not expect to get by without having to modify this
        test case.

        Some specific limitations of the static analysis:
         - No support for `for` loops, `do-while` loops, `switch`, ternary
             conditionals, `goto`, `asm`, attributes and more;
         - `while` loops are treated as executing 0 or 1 times;
         - No shortcut logic (e.g. `0 && lock()` would be considered lock
             acquisition);
         - No support for `break`;
         - No restriction on recursive acquisition of the semaphore (even
             though the one we're using doesn't support recursive acquisition);
         - No support for // style comments;
         - Probably more
        '''
        src = munge(os.path.join(MY_DIR, '../seL4Notification-to.template.c'))
        ast = parse(src)
        for node in ast.ext:
            # Test all contained functions.
            if isinstance(node, c_ast.FuncDef):
                check_termination(src, node.decl.name, node.body.block_items)

    def test_sel4notification_safety(self):
        pml = os.path.join(MY_DIR, 'sel4notification.pml')

        tmp = self.mkdtemp()

        subprocess.check_call(['spin', '-a', pml], cwd=tmp)

        pan_safety = os.path.join(tmp, 'pan-safety')
        subprocess.check_call(['gcc', '-o', pan_safety, '-O3', '-DREACH',
            '-DSAFETY', 'pan.c'], cwd=tmp, universal_newlines=True)

        p = subprocess.Popen([pan_safety], stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, universal_newlines=True)
        stdout, stderr = p.communicate()

        if p.returncode != 0:
            self.fail('pan-safety returned %s' % p.returncode)

        if stdout.find('errors: 0') < 0:
            self.fail('pan-safety failed:\n%s' % stdout)

    def test_sel4notification_liveness(self):
        pml = os.path.join(MY_DIR, 'sel4notification.pml')

        tmp = self.mkdtemp()

        subprocess.check_call(['spin', '-a', '-m', pml], cwd=tmp)

        pan_liveness = os.path.join(tmp, 'pan-safety')
        subprocess.check_call(['gcc', '-o', pan_liveness, '-O3', '-DNP',
            '-DNOREDUCE', 'pan.c'], cwd=tmp)

        p = subprocess.Popen([pan_liveness, '-l', 'm100000'],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True)
        stdout, stderr = p.communicate()

        if p.returncode != 0:
            self.fail('pan-liveness returned %s' % p.returncode)

        if stdout.find('errors: 0') < 0:
            self.fail('pan-liveness failed:\n%s' % stdout)

# A brief prelude to the seL4Notification-to.template.c source to give it some types
# it expects in the absence of the libsel4 headers.
HEADER = '''
    typedef int seL4_CPtr;
    typedef unsigned long seL4_Word;
'''

def munge(filename):
    '''
    Tweak the seL4Notification-to.template.c source to suppress some external
    references and constructs pycparser can't handle.
    '''
    stripped = reduce(lambda acc, x: re.sub(x[0], x[1], acc, flags=re.MULTILINE),

        # Turn template variable definitions into source variable definitions.
        ((r'/\*-\s*set\s+(notification|handoff|lock)\s*=.*?-\*/',
            r'static seL4_CPtr \g<1>;'),
        (r'/\*-\s*set\s+badge_magic\s*=.*?-\*/',
            r'static seL4_Word badge_magic;'),

        # Turn template variable reference into source variable references.
        (r'/\*\?\s*(notification|handoff|lock|badge_magic)\s*\?\*/', r'\g<1>'),

        # Remove comments.
        (r'/\*(.|\n)*?\*/', ''),

        # Remove usage of the UNUSED macro.
        (r'\sUNUSED\s', ' '),

        # Remove CPP directives.
        (r'^#.*?$', ''),

        # Remove CAmkES error invocations.
        (r'ERR\((.|\n)*?{(.|\n)*?}(.|\n)*?{(.|\n)*?}\)\);', '')),

        open(filename, 'rt').read())
    return '%s%s' % (HEADER, stripped)

def parse(string):
    '''
    Parse C source code into a pycparser AST.
    '''
    return c_parser.CParser().parse(string)

def lock_operations(statement):
    '''
    Find the number of `lock()` operations within a statement. Note that we
    count `unlock()` as -1 to compute a total. This function makes many
    simplifications, including performing no control flow analysis, and thus
    may be inaccurate.
    '''
    ops = 0
    if isinstance(statement, c_ast.FuncCall):
        if statement.name.name == 'lock':
            ops = 1
        elif statement.name.name == 'unlock':
            ops = -1

    # Descend into this node's children if it has any.
    if isinstance(statement, c_ast.Node):
        ops += sum(lock_operations(x) for x in statement.children())
    elif isinstance(statement, tuple):
        ops += sum(lock_operations(x) for x in statement)

    return ops

class LockProtocolError(Exception):
    '''
    An error indicating a failure to release a lock or too many lock releases
    on an exit path.
    '''

    def __init__(self, message, source, node=None):
        if node is not None:
            # Compute a pretty printed version of the source code indicating the
            # terminating line of execution that leads to the error.
            content = six.cStringIO()
            for lineno, line in enumerate(source.split('\n')):
                content.write('%s %s\n' %
                    ('>' if lineno == int(node.coord.line) else ' ', line))
            super(LockProtocolError, self).__init__('%s\n%s' %
                (message, content.getvalue()))
        else:
            super(LockProtocolError, self).__init__(message)

def check_termination(source, name, statements, accumulated=None, locks=0):
    '''
    Ensure the lock protocol is preserved on all paths through this series of
    statements.

     source - source code containing these statements (for diagnostics)
     name - name of the containing function
     statements - statements to analyse
     accumulated - statements we have passed leading up to the current series
     locks - number of locks we currently hold
    '''

    if accumulated is None:
        accumulated = []

    if statements is None:
        statements = []

    for index, statement in enumerate(statements):

        if isinstance(statement, c_ast.While):
            # For `while` loops, we assume the condition is always evaluated
            # and then the body is executed either 0 or 1 times. The recursive
            # call here is the 1 case and the continuing (fall through)
            # execution is the 0 case.
            locks += lock_operations(statement.cond)
            if locks < 0:
                raise LockProtocolError('lock release while no lock held in '
                    '%s at line %s' % (name, statement.coord.line), source,
                    statement)
            check_termination(source, name, statement.stmt.block_items +
                statements[index+1:], accumulated + statements[:index+1],
                locks)

        elif isinstance(statement, c_ast.If):
            # For `if` statements, we assume any lock operations in the
            # condition expression are only relevant for the else branch. This
            # is based on the following idiom for taking a lock:
            #
            #     if (lock() != 0) {
            #         /* failure case; lock() should not be counted */
            #     } else {
            #         /* success case; lock() should be counted */
            #     }

            # If branch.
            check_termination(source, name, ([statement.iftrue] if
                statement.iftrue is not None else []) + statements[index+1:],
                accumulated + statements[:index+1], locks)

            # Else branch.
            locks += lock_operations(statement.cond)
            if locks < 0:
                raise LockProtocolError('lock release while no lock held in '
                    '%s at else branch of line %s' % (name,
                    statement.coord.line), source, statement)
            check_termination(source, name, ([statement.iffalse] if
                statement.iffalse is not None else []) + statements[index+1:],
                accumulated + statements[:index+1], locks)

            # Together, the recursive calls have handled the remainder of this
            # function, so no need to continue.
            return

        elif isinstance(statement, (c_ast.Return, c_ast.Continue)):
            # We've reached a termination point of this function. Note that we
            # count a `continue` statement as a point of termination. This is
            # based on the following idiom for restarting a function, which we
            # assume is the only use of `continue`:
            #
            #     void foo() {
            #         while (true) {
            #             ...
            #             continue; /* restart function */
            #             ...
            #         }
            #     }

            # Take into account any lock operations in the return expression
            # itself, though we expect there to be none.
            locks += lock_operations(statement)

            if locks > 0:
                raise LockProtocolError('%s locks potentially held when '
                    'exiting %s at line %s' % (locks, name,
                    statement.coord.line), source, statement)
            elif locks < 0:
                raise LockProtocolError('%s too many lock releases '
                    'potentially executed before exiting %s at line %s' %
                    (-locks, name, statement.coord.line), source, statement)

            # Otherwise, we're good.

            return

        elif isinstance(statement, c_ast.Compound):
            # Statement block. Recurse into it.
            check_termination(source, name, (statement.block_items or []) +
                statements[index+1:], accumulated + statements[:index+1],
                locks)
            return

        else:
            # Regular statement. Count its locks.
            locks += lock_operations(statement)

    # If we reached here, this function terminated without a return statement
    # (perfectly valid for a `void` function).

    # Find the last statement executed in case we need to raise an exception.
    if len(statements) > 0:
        last = statements[-1]
    elif len(accumulated) > 0:
        last = accumulated[-1]
    else:
        last = None

    if last is None:
        location = 'end of function'
    else:
        location = 'line %s' % last.coord.line

    if locks > 0:
        raise LockProtocolError('%s locks potentially held when exiting %s at '
            '%s' % (locks, name, location), source, last)
    elif locks < 0:
        raise LockProtocolError('%s too many lock releases potentially '
            'executed before exiting %s at %s' % (-locks, name, location),
            source, last)

    # If we reached here, the function conformed to the protocol in an
    # execution that reached its end.

if __name__ == '__main__':
    unittest.main()
