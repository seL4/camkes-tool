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

'''This is a simple lint checker for Jinja templates. It is designed to catch
the common errors of either mismatching /*- ... -*/ blocks or using /*? ... ?*/
instead of /*- ... -*/.'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import abc, collections, re, six, sys

class Tokeniser(six.with_metaclass(abc.ABCMeta, collections.Iterator)):
    '''
    Basic Jinja file tokeniser interface. Two implementations of this follow
    below.
    '''
    def __init__(self, filename):
        with open(filename, 'rt') as f:
            self.data = f.read()
        self.regex = None
        self.index = 0
        self.line = 1

    def __iter__(self):
        return self

    def __next__(self):
        assert self.regex is not None
        while True:
            token = self.regex.search(self.data, self.index)
            if token is None:
                raise StopIteration
            self.index = token.end()
            if token.group(1) == '\n':
                self.line += 1
                continue
            text = token.groups()[1:]
            break
        return text

    def next(self):
        return self.__next__()

class LowTokeniser(Tokeniser):
    '''
    A tokeniser for recognising the matching Jinja special symbols ("/*-" and
    friends.
    '''
    def __init__(self, filename):
        super(LowTokeniser, self).__init__(filename)
        self.regex = re.compile(r'(?:(\n)|(/\*[-\?#]|[-\?#]\*/))',
            flags=re.MULTILINE)

class HighTokeniser(Tokeniser):
    '''
    A tokeniser for recognising Jinja directives ("/*- if .... -*/" and
    friends).
    '''
    def __init__(self, filename):
        super(HighTokeniser, self).__init__(filename)
        self.regex = re.compile(r'(?:(\n)|/\*-[-\+]?[\s]*([\S]+)\s(.*?)\s*[-\+]?-\*/)',
            flags=re.MULTILINE)

def main():
    if len(sys.argv) < 2:
        sys.stderr.write('Usage: %s template\n' % sys.argv[0])
        return -1

    # First try to find any low-level errors (mismatched /*. .*/). We do this
    # first because, if there are problems here, it will likely cause a high
    # level error that will be harder to trace back to the source.

    t = LowTokeniser(sys.argv[1])

    last = None
    starter = re.compile(r'/\*.$')

    for token, in t:
        if starter.match(token) is not None:
            if last is not None:
                raise SyntaxError('%s:%d: opening %s while still inside '
                    'preceding %s' % (sys.argv[1], t.line, token, last))
            last = token
        elif last is None:
            raise SyntaxError('%s:%d: closing %s while not inside a Jinja '
                'directive' % (sys.argv[1], t.line, token))
        else:
            assert last in ('/*-', '/*#', '/*?'), 'unexpected last token ' \
                '\'%s\' recorded (bug in linter?)' % last
            assert token in ('-*/', '#*/', '?*/'), 'unexpected token \'%s\' ' \
                'recognised (bug in linter?)' % token
            if last[2] != token[0]:
                raise SyntaxError('%s:%d: closing %s while inside %s block' %
                    (sys.argv[1], t.line, token, last))
            last = None

    # Now try to find any high-level errors (mismatched valid Jinja
    # directives).

    stack = []

    t = HighTokeniser(sys.argv[1])

    DO_WORD_MATCH = re.compile(r'\w*$')
    SET_MATCH = re.compile(r'.*?\S\s*=\s*\S')

    for token, content in t:
        if token in ['if', 'for', 'macro']:
            stack.append(token)
        elif token == 'endif':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endif while not inside a block' %
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'if':
                raise SyntaxError('%s:%d: endif while inside a %s block' %
                    (sys.argv[1], t.line, context))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in an endif '
                    'statement' % (sys.argv[1], t.line, content))
        elif token == 'elif':
            if len(stack) == 0 or stack[-1] != 'if':
                raise SyntaxError('%s:%d: %s while not inside an if block' %
                    (sys.argv[1], t.line, token))
        elif token == 'else':
            if len(stack) == 0 or stack[-1] not in ['if', 'for']:
                raise SyntaxError('%s:%d: %s while not inside an if or for block' %
                    (sys.argv[1], t.line, token))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in an else '
                    'statement' % (sys.argv[1], t.line, content))
            if stack[-1] == 'for':
                # This is not a guaranteed error, but more of a code smell. The
                # semantics of this construct in Jinja mean it is almost always
                # indicative of a mistake.
                sys.stderr.write('%s:%d: warning: else inside for block; this '
                    'has different semantics to Python\n' % (sys.argv[1],
                    t.line))
        elif token == 'endfor':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endfor while not inside a block' %
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'for':
                raise SyntaxError('%s:%d: endfor while inside a %s block' %
                    (sys.argv[1], t.line, context))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in an endfor '
                    'statement' % (sys.argv[1], t.line, content))
        elif token == 'endmacro':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endmacro while not inside a block' %
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'macro':
                raise SyntaxError('%s:%d: endmacro while inside a %s block' %
                    (sys.argv[1], t.line, context))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in an endmacro '
                    'statement' % (sys.argv[1], t.line, content))
        elif token == 'break':
            if 'for' not in stack:
                raise SyntaxError('%s:%d: break while not inside a for block' %
                    (sys.argv[1], t.line))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in a break '
                    'statement' % (sys.argv[1], t.line, content))
        elif token == 'continue':
            if 'for' not in stack:
                raise SyntaxError('%s:%d: continue while not inside a for block' %
                    (sys.argv[1], t.line))
            if content != '':
                raise SyntaxError('%s:%d: trailing content \'%s\' in a continue '
                    'statement' % (sys.argv[1], t.line, content))
        elif token == 'do':
            if DO_WORD_MATCH.match(content) is not None:
                raise SyntaxError('%s:%d: seemingly incorrect expression '
                    '\'%s\' in do statement' % (sys.argv[1], t.line, content))
        elif token == 'set':
            if SET_MATCH.match(content) is None:
                raise SyntaxError('%s:%d: seemingly incorrect expression '
                    '\'%s\' in set statement' % (sys.argv[1], t.line, content))
        elif token in ['import', 'include']:
            # Ignore; allowable anywhere.
            pass
        else:
            raise SyntaxError('%s:%d: unknown directive %s' %
                (sys.argv[1], t.line, token))

    if len(stack) != 0:
        raise SyntaxError('%s: open %s when reaching end of file' %
            (sys.argv[1], stack[-1]))

    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except SyntaxError as e:
        sys.stderr.write('%s\n' % str(e))
        sys.exit(-1)
