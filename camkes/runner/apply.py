#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Helper functions for generating apply-style proof scripts. These are designed
to be called from a template context, not from Python. When using these
functions you should not indent your template code at all. Example usage:

  lemma "A \<or> B \<Longrightarrow> B \<or> A"
  /*? apply('erule disjE', solves=-1) ?*/
  /*? apply('rule disjI2') ?*/
  /*? apply('assumption', solves=1) ?*/
  /*? apply('rule disjI1') ?*/
  /*? apply('assumption', solves=1) ?*/
  /*? done ?*/
'''

INITIAL_INDENT = '  '

subgoals = 1

def wrap(tactic):
    if ' ' in tactic and not tactic.startswith('('):
        return '(%s)' % tactic
    return tactic

def apply(tactic, solves=0):
    global subgoals

    s = '%(init)s%(indent)sapply %(tactic)s' % {
        'init':INITIAL_INDENT,
        'indent':(subgoals - 1) * ' ',
        'tactic':wrap(tactic),
    }
    subgoals -= solves
    return s

class ProofCompleter(object):
    '''A command that finishes a proof.'''
    def __init__(self, token):
        self.token = token

    def __repr__(self):
        global subgoals
        subgoals = 1
        return '%s%s' % (INITIAL_INDENT, self.token)

    def __call__(self):
        return str(self)

def by(tactic):
    return ProofCompleter('by %s' % wrap(tactic))

done = ProofCompleter('done')
sorry = ProofCompleter('sorry')
oops = ProofCompleter('oops')
