#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import camkes.ast as AST
import itertools

class Problem(object):
    '''Generic type for problems with an AST. This is expected to never be
    instantiated directly. You should use ProblemWarning and ProblemError
    below.'''
    def __init__(self, check_name, msg, filename, lineno):
        self.msg = msg
        self.filename = filename
        self.lineno = lineno
        self.check_name = check_name

    def __repr__(self):
        return '%s:%d: %s' % (self.filename, self.lineno, self.msg)

class ProblemWarning(Problem):
    def __repr__(self):
        return 'Warning: %s' % super(ProblemWarning, self).__repr__()

class ProblemError(Problem):
    def __repr__(self):
        return 'Error: %s' % super(ProblemError, self).__repr__()

# Start of check definitions. If you want to write your own check, implement it
# as a function below that takes an AST and yields ProblemWarnings and
# ProblemErrors. Remember to add it to CHECKS below to enable it.

def no_references(ast):
    '''Check whether there are unresolved references in the AST.'''
    for i in ast:
        if isinstance(i, AST.Reference) and i._referent is None:
            yield ProblemWarning('no_references', \
                'Unresolved reference to \'%s\'' % i._symbol, i.filename, \
                i.lineno)
        elif not isinstance(i, AST.Reference):
            for j in no_references(i.children()):
                yield j

# List of checks to run. Each check should be a callable that takes a list of
# ASTObjects.
CHECKS = [
    no_references,
]

def check(ast):
    '''Run all registered AST checks.'''
    assert isinstance(ast, list)
    for i in ast: assert isinstance(i, AST.ASTObject)

    return itertools.chain(*map(lambda x:x(ast), CHECKS))
