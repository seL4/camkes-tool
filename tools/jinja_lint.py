#!/usr/bin/env python3
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

import abc, collections.abc, re, sys
from typing import Optional

class Tokeniser(collections.abc.Iterator, metaclass=abc.ABCMeta):
    '''
    Basic Jinja file tokeniser interface. Two implementations of this follow
    below.
    '''
    def __init__(self, filename: str):
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
    def __init__(self, filename: str):
        super().__init__(filename)
        self.regex = re.compile(r'(?:(\n)|(/\*[-\?#]|[-\?#]\*/))',
            flags=re.MULTILINE)

class HighTokeniser(Tokeniser):
    '''
    A tokeniser for recognising Jinja directives ("/*- if .... -*/" and
    friends).
    '''
    def __init__(self, filename: str):
        super().__init__(filename)
        self.regex = re.compile(r'(?:(\n)|/\*-[-\+]?[\s]*([^\s(]+)(?:\([^)]*\))?\s(.*?)\s*[-\+]?-\*/)',
            flags=re.MULTILINE)

def main() -> int:

    if len(sys.argv) < 2:
        sys.stderr.write(f'Usage: {sys.argv[0]} template\n')
        return -1

    # First try to find any low-level errors (mismatched /*. .*/). We do this
    # first because, if there are problems here, it will likely cause a high
    # level error that will be harder to trace back to the source.

    t = LowTokeniser(sys.argv[1])

    last: Optional[str] = None
    starter = re.compile(r'/\*.$')

    for token, in t:
        if starter.match(token) is not None:
            if last is not None:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: opening {token} '
                  f'while still inside preceding {last}')
            last = token
        elif last is None:
            raise SyntaxError(f'{sys.argv[1]}:{t.line}: closing {token} while '
              'not inside a Jinja directive')
        else:
            assert last in ('/*-', '/*#', '/*?'), 'unexpected last token ' \
                f'\'{last}\' recorded (bug in linter?)'
            assert token in ('-*/', '#*/', '?*/'), 'unexpected token ' \
                f'\'{token}\' recognised (bug in linter?)'
            if last[2] != token[0]:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: closing {token} '
                  f'while inside {last} block')
            last = None

    # Now try to find any high-level errors (mismatched valid Jinja
    # directives).

    stack: [str] = []

    t = HighTokeniser(sys.argv[1])

    DO_WORD_MATCH = re.compile(r'\w*$')
    SET_MATCH = re.compile(r'.*?\S\s*=\s*\S')

    for token, content in t:
        if token in ['if', 'for', 'macro', 'call']:
            stack.append(token)
        elif token == 'endif':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{sys.argv[1]}:{t.line}: endif while not inside a block')
            context = stack.pop()
            if context != 'if':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: endif while inside '
                  f'a {context} block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in an endif statement')
        elif token == 'elif':
            if len(stack) == 0 or stack[-1] != 'if':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: {token} while not '
                  'inside an if block')
        elif token == 'else':
            if len(stack) == 0 or stack[-1] not in ['if', 'for']:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: {token} while not '
                  'inside an if or for block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in an else statement')
            if stack[-1] == 'for':
                # This is not a guaranteed error, but more of a code smell. The
                # semantics of this construct in Jinja mean it is almost always
                # indicative of a mistake.
                sys.stderr.write(f'{sys.argv[1]}:{t.line}: warning: else '
                  'inside for block; this has different semantics to Python\n')
        elif token == 'endfor':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{sys.argv[1]}:{t.line}: endfor while not inside a block')
            context = stack.pop()
            if context != 'for':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: endfor while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in an endfor statement')
        elif token == 'endmacro':
            if len(stack) == 0:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: endmacro while not '
                  'inside a block')
            context = stack.pop()
            if context != 'macro':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: endmacro while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in an endmacro statement')
        elif token == 'endcall':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{sys.argv[1]}:{t.line}: endcall while not inside a block')
            context = stack.pop()
            if context != 'call':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: endcall while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in an endcall statement')
        elif token == 'break':
            if 'for' not in stack:
                raise SyntaxError(
                  f'{sys.argv[1]}:{t.line}: break while not inside a for block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in a break statement')
        elif token == 'continue':
            if 'for' not in stack:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: continue while not '
                  'inside a for block')
            if content != '':
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: trailing content '
                  f'\'{content}\' in a continue statement')
        elif token == 'do':
            if DO_WORD_MATCH.match(content) is not None:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: seemingly '
                  f'incorrect expression \'{content}\' in do statement')
        elif token == 'set':
            if SET_MATCH.match(content) is None:
                raise SyntaxError(f'{sys.argv[1]}:{t.line}: seemingly '
                  f'incorrect expression \'{content}\' in set statement')
        elif token in ['import', 'include', 'from']:
            # Ignore; allowable anywhere.
            pass
        else:
            raise SyntaxError(
              f'{sys.argv[1]}:{t.line}: unknown directive {token}')

    if len(stack) != 0:
        raise SyntaxError(f'{sys.argv[1]}: open {stack[-1]} when reaching end '
          'of file')

    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except SyntaxError as e:
        sys.stderr.write(f'{e}\n')
        sys.exit(-1)
