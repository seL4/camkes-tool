#!/usr/bin/env python
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
Generate a BNF representation of a PLY parser.

This script takes a set of PLY Python sources describing zero or more of the
following:
 - A set of keywords in the variable 'keywords';
 - A set of tokens defined as variables or functions in PLY style with the 't_'
   prefix; and/or
 - A set of production rules defined as functions in the PLY style with the
   'p_' prefix.
It merges these entities from all the files you have passed and then prints a
BNF grammar based on these collections.

A simple way of generating a BNF grammar for the parser in this repository is:
 find ../parser -name "*.py" | xargs ./to-bnf.py
'''

import datetime, imp, os, sys

def isfunction(f): return hasattr(f, '__call__')

def strip(s): return s.strip()

def main():
    if len(sys.argv) == 1:
        print >>sys.stderr, 'Usage: %s <PLY files>' % sys.argv[0]
        return -1

    keywords = set()
    tokens = {}
    rules = {}

    for f in sys.argv[1:]:
        # Import each source as 'mod'
        try:
            sys.path.append(os.path.dirname(f))
            mod = imp.load_source('', f)
        except IOError:
            print >>sys.stderr, 'Failed to import %s' % f
            return -1
        
        # Merge any keywords
        if 'keywords' in mod.__dict__:
            assert isinstance(mod.keywords, set)
            keywords = keywords.union(mod.keywords)

        # Merge any tokens
        for t in filter(lambda x: x.startswith('t_') and \
                                  x not in ['t_ignore', 't_error'], \
                        mod.__dict__):
            token_obj = mod.__dict__[t]
            token = t[2:]
            if isfunction(token_obj):
                tokens[token] = token_obj.__doc__
            else:
                # Token is a variable
                tokens[token] = token_obj

        # Merge any rules
        for p in filter(lambda x: x.startswith('p_') and \
                                  x != 'p_error', mod.__dict__):
            rule = mod.__dict__[p]
            assert isfunction(rule)
            parts = map(strip, rule.__doc__.split(':'))
            assert len(parts) == 2
            sym = parts[0]
            expansion = parts[1]
            rules[sym] = map(strip, expansion.split('|'))

    # Print the resulting BNF grammar
    print '# BNF grammar generated from:'
    print '#  %s' % ' '.join(sys.argv)
    print '# Generated at %s\n' % datetime.datetime.now().isoformat()

    print '# Rules'
    for r in rules:
        print '%s :' % r,
        print (' ' * len(r) + ' | ').join(map(lambda x: x + '\n', rules[r])),
        print ' ' * len(r) + ' ;'

    print '\n# Tokens'
    for t in tokens:
        print '%s : "%s";' % (t, tokens[t])

    print '\n# Keywords'
    for k in keywords:
        print '%s : "%s";' % (k, k)

    return 0

if __name__ == '__main__':
    sys.exit(main())
