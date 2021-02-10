#!/usr/bin/env python3
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''This is a simple lint checker for Jinja templates. It is designed to catch
the common errors of either mismatching {% ... %} blocks or using {{ ... }}
instead of {% ... %}.'''

import argparse, re, sys
from typing import Generator, IO, Optional, Tuple

# command line options that will be set from main()
options = None

def low_tokeniser(file: IO[str]) -> Generator[Tuple[int, str], None, None]:
    '''
    A tokeniser for recognising the matching Jinja special symbols.
    '''
    for line_index, content in enumerate(file):
        i = 0
        while i < len(content):
            for text in (options.block_start,
                         options.block_end,
                         options.variable_start,
                         options.variable_end,
                         options.comment_start,
                         options.comment_end):
                if content[i:i+len(text)] == text:
                    yield line_index + 1, text
                    i += len(text)
                    break
            else:
                i += 1

def high_tokeniser(file: IO[str]) -> Generator[Tuple[int, str, str], None, None]:
    '''
    A tokeniser for recognising Jinja directives.
    '''
    content = file.read()
    lineno = 1
    i = 0
    while i < len(content):

        # find the next start of a block
        bs = content.find(options.block_start, i)
        if bs == -1: # none found
            break

        # adjust the line counter to be accurate
        lineno += content.count('\n', i, bs)

        # determine the end of the start string
        bs_end = bs + len(options.block_start)

        # account for the optional white space control '+' or '-'
        if len(content) > bs_end and content[bs_end] in ('-', '+'):
            bs_end += 1

        # find the end of this block
        be = content.find(options.block_end, bs_end)
        if be == -1: # not found
            break

        # determine the end of the end string
        be_end = be + len(options.block_end)

        # similarly, account for the optional white space control
        if be > bs_end and content[be-1] in ('-', '+'):
            be -= 1

        # extract the directive of this block
        m = re.match(r'\s*\w+', content[bs_end:be])
        if m is not None: # we have a directive

            directive = m.group(0).strip()
            offset = len(m.group(0))
            remainder = content[bs_end+offset:be]

            yield lineno, directive, remainder.strip()

        lineno += content.count('\n', bs, be_end)
        i = be_end

def main(args: [str]) -> int:

    # parse command line arguments
    global options
    parser = argparse.ArgumentParser(description='Jinja linter')
    parser.add_argument('--block-start', default='{%')
    parser.add_argument('--block-end', default='%}')
    parser.add_argument('--variable-start', default='{{')
    parser.add_argument('--variable-end', default='}}')
    parser.add_argument('--comment-start', default='{#')
    parser.add_argument('--comment-end', default='#}')
    parser.add_argument('file', type=argparse.FileType('rt'))
    options = parser.parse_args(args[1:])

    filename = options.file.name

    # First try to find any low-level errors (mismatched {. .}). We do this
    # first because, if there are problems here, it will likely cause a high
    # level error that will be harder to trace back to the source.

    last: Optional[str] = None

    def is_starter(text: str) -> bool:
        return text in (options.block_start, options.variable_start,
            options.comment_start)

    def is_ender(text: str) -> bool:
        return text in (options.block_end, options.variable_end,
            options.comment_end)

    def paired(start: str, end: str) -> bool:
        if start == options.block_start and end == options.block_end:
            return True
        if start == options.variable_start and end == options.variable_end:
            return True
        if start == options.comment_start and end == options.comment_end:
            return True
        return False


    for lineno, token in low_tokeniser(options.file):
        if is_starter(token):
            if last is not None:
                raise SyntaxError(f'{filename}:{lineno}: opening {token} '
                  f'while still inside preceding {last}')
            last = token
        elif last is None:
            raise SyntaxError(f'{filename}:{lineno}: closing {token} while '
              'not inside a Jinja directive')
        else:
            assert is_starter(last), 'unexpected last token ' \
                f'\'{last}\' recorded (bug in linter?)'
            assert is_ender(token), 'unexpected token ' \
                f'\'{token}\' recognised (bug in linter?)'
            if not paired(last, token):
                raise SyntaxError(f'{filename}:{lineno}: closing {token} '
                  f'while inside {last} block')
            last = None

    # rewind the file pointer so we can reuse it in the next tokeniser
    options.file.seek(0)

    # Now try to find any high-level errors (mismatched valid Jinja
    # directives).

    stack: [str] = []

    DO_WORD_MATCH = re.compile(r'\w*$')
    SET_MATCH = re.compile(r'.*?\S\s*=\s*\S')

    for lineno, token, content in high_tokeniser(options.file):
        if token in ['if', 'for', 'macro', 'call']:
            stack.append(token)
        elif token == 'endif':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{filename}:{lineno}: endif while not inside a block')
            context = stack.pop()
            if context != 'if':
                raise SyntaxError(f'{filename}:{lineno}: endif while inside '
                  f'a {context} block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in an endif statement')
        elif token == 'elif':
            if len(stack) == 0 or stack[-1] != 'if':
                raise SyntaxError(f'{filename}:{lineno}: {token} while not '
                  'inside an if block')
        elif token == 'else':
            if len(stack) == 0 or stack[-1] not in ['if', 'for']:
                raise SyntaxError(f'{filename}:{lineno}: {token} while not '
                  'inside an if or for block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in an else statement')
            if stack[-1] == 'for':
                # This is not a guaranteed error, but more of a code smell. The
                # semantics of this construct in Jinja mean it is almost always
                # indicative of a mistake.
                sys.stderr.write(f'{filename}:{lineno}: warning: else '
                  'inside for block; this has different semantics to Python\n')
        elif token == 'endfor':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{filename}:{lineno}: endfor while not inside a block')
            context = stack.pop()
            if context != 'for':
                raise SyntaxError(f'{filename}:{lineno}: endfor while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in an endfor statement')
        elif token == 'endmacro':
            if len(stack) == 0:
                raise SyntaxError(f'{filename}:{lineno}: endmacro while not '
                  'inside a block')
            context = stack.pop()
            if context != 'macro':
                raise SyntaxError(f'{filename}:{lineno}: endmacro while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in an endmacro statement')
        elif token == 'endcall':
            if len(stack) == 0:
                raise SyntaxError(
                  f'{filename}:{lineno}: endcall while not inside a block')
            context = stack.pop()
            if context != 'call':
                raise SyntaxError(f'{filename}:{lineno}: endcall while '
                  f'inside a {context} block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in an endcall statement')
        elif token == 'break':
            if 'for' not in stack:
                raise SyntaxError(
                  f'{filename}:{lineno}: break while not inside a for block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in a break statement')
        elif token == 'continue':
            if 'for' not in stack:
                raise SyntaxError(f'{filename}:{lineno}: continue while not '
                  'inside a for block')
            if content != '':
                raise SyntaxError(f'{filename}:{lineno}: trailing content '
                  f'\'{content}\' in a continue statement')
        elif token == 'do':
            if DO_WORD_MATCH.match(content) is not None:
                raise SyntaxError(f'{filename}:{lineno}: seemingly '
                  f'incorrect expression \'{content}\' in do statement')
        elif token == 'set':
            if SET_MATCH.match(content) is None:
                raise SyntaxError(f'{filename}:{lineno}: seemingly '
                  f'incorrect expression \'{content}\' in set statement')
        elif token in ['import', 'include', 'from']:
            # Ignore; allowable anywhere.
            pass
        else:
            raise SyntaxError(
              f'{filename}:{lineno}: unknown directive {token}')

    if len(stack) != 0:
        raise SyntaxError(f'{filename}: open {stack[-1]} when reaching end '
          'of file')

    return 0

if __name__ == '__main__':
    try:
        sys.exit(main(sys.argv))
    except SyntaxError as e:
        sys.stderr.write(f'{e}\n')
        sys.exit(-1)
