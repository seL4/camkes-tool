#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''Common lexing tokens relevant for all grammars. See accompanying docs for
more information.'''

import sys
from .. import util

t_COMMA = r','
t_DOT = r'\.'
t_EQUALS = r'='
t_LBRACE = r'{'
t_LPAREN = r'\('
t_LSQUARE = r'\['
t_RBRACE = r'}'
t_RPAREN = r'\)'
t_RSQUARE = r'\]'
t_SEMI = r';'

# Ignore whitespace.
t_ignore = ' \t\r'

def t_STRING(t):
    r'"[^"]*"'
    t.value = t.value[1:-1] # Strip quotes
    return t

def t_NUMBER(t):
    r'-?[0-9][0-9]*'
    t.value = int(t.value)
    return t

def t_DECIMAL(t):
    r'-?[0-9]+\.?[0-9]*'
    t.value = float(t.value)
    return t

def t_ANGLE_STRING(t):
    r'<[^>]*>'
    t.value = t.value[1:-1] # Strip angle brackets
    return t

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*'
    if t.value in util.keywords:
        t.type = t.value
    return t

# Track line number via new line characters, as per 4.6 of the PLY docs.
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_COMMENT(t):
    r'(/\*(.|\n)*?\*/)|(//.*)'
    # Ignore comments, but account for encountered new lines.
    t.lexer.lineno += t.value.count('\n')

def t_error(t):
    print >>sys.stderr, '%d: Illegal token \'%s\'' % (t.lineno, t.value[0])
    t.lexer.skip(1)
