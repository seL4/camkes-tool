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

'''This is a simple lint checker for Jinja templates. It is designed to catch
the common errors of either mismatching /*- ... -*/ blocks or using /*? ... ?*/
instead of /*- ... -*/.'''

import re, sys

class Tokeniser:
    def __init__(self, filename):
        with open(filename, 'r') as f:
            self.data = f.read()
        self.regex = re.compile(r'(?:(\n)|/\*-[\s]*([\S]+)\s.*?-\*/)', flags=re.MULTILINE)
        self.index = 0
        self.line = 1

    def __iter__(self):
        return self

    def __next__(self):
        while True:
            token = self.regex.search(self.data, self.index)
            if token is None:
                raise StopIteration
            self.index = token.end()
            if token.group(1) == '\n':
                self.line += 1
                continue
            text = token.group(2)
            break
        return text

    def next(self):
        return self.__next__()

def main():
    if len(sys.argv) < 2:
        print >>sys.stderr, 'Usage: %s template' % sys.argv[0]
        return -1

    stack = []

    t = Tokeniser(sys.argv[1])

    for token in t:
        if token in ['if', 'for', 'macro']:
            stack.append(token)
        elif token == 'endif':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endif while not inside a block' % \
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'if':
                raise SyntaxError('%s:%d: endif while inside a %s block' % \
                    (sys.argv[1], t.line, context))
        elif token in ['elif', 'else']:
            if len(stack) == 0 or stack[-1] != 'if':
                raise SyntaxError('%s:%d: %s while not inside an if block' % \
                    (sys.argv[1], t.line, token))
        elif token == 'endfor':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endfor while not inside a block' % \
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'for':
                raise SyntaxError('%s:%d: endfor while inside a %s block' % \
                    (sys.argv[1], t.line, context))
        elif token == 'endmacro':
            if len(stack) == 0:
                raise SyntaxError('%s:%d: endmacro while not inside a block' % \
                    (sys.argv[1], t.line))
            context = stack.pop()
            if context != 'macro':
                raise SyntaxError('%s:%d: endmacro while inside a %s block' % \
                    (sys.argv[1], t.line, context))
        elif token == 'break':
            if len(stack) == 0 or stack[-1] not in ['for', 'if']:
                raise SyntaxError('%s:%d: break while not inside a for or if' % \
                    (sys.argv[1], t.line))
        elif token == 'continue':
            if 'for' not in stack:
                raise SyntaxError('%s:%d: continue while not inside a for' % \
                    (sys.argv[1], t.line))
        elif token in ['do', 'include', 'set']:
            # Ignore; allowable anywhere.
            pass
        else:
            raise SyntaxError('%s:%d: unknown directive %s' % \
                (sys.argv[1], t.line, token))

    if len(stack) != 0:
        raise SyntaxError('%s: open %s when reaching end of file' % \
            (sys.argv[1], stack[-1]))

    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except SyntaxError as e:
        print >>sys.stderr, str(e)
        sys.exit(-1)
