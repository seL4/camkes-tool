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
Top-level functionality of the CAmkES parser. You should not access this file
directly, but should instead import the camkes.parser module and only use the
symbols exported in __init__.py.
TODO: Rename this file to something more sensible.
'''

import logging, os, subprocess

import camkes.internal.log as log

import ply.lex as lex
import ply.yacc as yacc

import util

# Extra keywords
from input import ADLKeywords, IDLKeywords

# Tokens need to be imported into our namespace so t_* symbols are in globals()
# for lex.lex().
from input.GenericTokens import *

# Parsing rules. These need to be imported into our namespace so p_* symbols
# are in globals() for yacc.yacc().
from input.ADLRules import *
from input.CAmkESRules import *
from input.IDLRules import *
from input.GenericRules import *

import camkes.ast as AST

# Post processing
import Resolution

def show(o):
    '''Convert an AST object (or list of AST objects) into a string
    representation.'''
    if isinstance(o, list):
        return '\n'.join(map(str, o))
    else:
        str(o)

def pretty(s):
    indent = '  '
    indent_level = 0
    whitespace = ' \t\n\r'
    p = ''
    reading_whitespace = False
    start_of_line = True
    for i in s:
        if i in whitespace:
            if reading_whitespace or start_of_line:
                continue
            else:
                reading_whitespace = True
                p += ' '
        else:
            reading_whitespace = False
            if i == '}':
                indent_level -= 1
                if not start_of_line:
                    p += '\n'
                p += '%s}\n' % (indent * indent_level)
                start_of_line = True
                continue
            if start_of_line:
                p += indent * indent_level
                start_of_line = False
            p += i
            if i == ';':
                p += '\n'
                start_of_line = True
            elif i == '{':
                p += '\n'
                indent_level += 1
                start_of_line = True
    return p

def resolve_references(ast):
    return Resolution.resolve_references(ast)

def assign_filenames(ast, filename):
    '''Set the given filename as the source for any items in the AST that don't
    have a current filename.'''
    for i in ast:
        if i.filename is None:
            i.filename = filename
        assign_filenames(i.children(), filename)

def parse_to_ast(s, cpp=False, cpp_flags=[], optimise=False):
    '''Build a lexer and parser for the given grammar and then parse the string
    s.'''

    if isinstance(s, str):
        filename = None
    else:
        # Assume s is a file handle.
        filename = s.name
        s = s.read()

    # Pre-process the source with CPP if requested.
    if cpp:
        toolprefix = os.environ.get('TOOLPREFIX', '')
        p = subprocess.Popen(['%scpp' % toolprefix, '-P'] + cpp_flags,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        if filename is not None:
            s = ('#line 0 "%s"\n' % filename) + s
        stdout, stderr = p.communicate(s)
        if p.returncode != 0: #pylint: disable=E1101
            raise Exception('CPP failed: %s' % stderr)
        s = stdout

    log.info('Building keyword list...')
    # The ID token rule relies on checking whether the matched token is one of
    # a reserved set of keywords. We need to build that list (in util) before
    # doing any lexing.
    util.reset_keywords()
    util.merge_keywords(IDLKeywords.keywords)
    util.merge_keywords(ADLKeywords.keywords)
    log.info('Done')

    log.info('Building token list...')
    # lex expects a list of valid tokens to be defined in the variable
    # 'tokens'. This is quite annoying because the list of tokens can be
    # deduced automatically (which is what get_tokens() does) and there is no
    # nice way of namespacing tokens. This means that building the parser below
    # will generate spurious warnings about unused tokens if you are only
    # parsing a subset of the CAmkES grammar.
    tokens = util.get_tokens(globals())
    log.info('Done')

    # Lex and Yacc accept a logger to notify the caller of events, but they are
    # really noisy; much more so than is relevant for our purposes. Squash
    # their output unless the user has specifically requested it.
    errorlog = log.log if log.log.getEffectiveLevel() < logging.WARNING \
                       else lex.NullLogger()

    # Enable optimised lexer and parser construction if the caller has
    # requested it. See the PLY docs for the exact effect of this.
    optimize = 1 if optimise else 0

    log.info('Building lexer...')
    try:
        lex.lex(errorlog=errorlog, optimize=optimize).filename = filename
    except Exception as inst:
        raise Exception('Failed to build lexer: %s' % str(inst))
    log.info('Done')

    # yacc by default assumes the starting token is the first one it lexically
    # encounters in globals(). This is almost certainly *not* the behaviour we
    # want so explicitly direct it by specifying the start symbol according to
    # the grammar we are trying to parse.
    start = 'camkes'

    log.info('Building parser...')
    try:
        yacc.yacc(errorlog=errorlog, optimize=optimize)
    except Exception as inst:
        raise Exception('Failed to build parser: %s' % str(inst))
    log.info('Done\n')

    ast = yacc.parse(s)

    # Set the source filename of the AST items if we know it.
    assign_filenames(ast, filename)

    return ast

def resolve_imports(ast, curdir, includepath=None, cpp=False, cpp_flags=[],
        optimise=False):
    '''Resolve any 'import' statements encountered in an AST. This takes
    the directory of the current file (for relative imports) and
    a list of paths to search for built-in imports. Note that files are not
    checked to be readable before opening. Also note that passing an AST to
    this function implicitly tells it to recursively resolve imports in
    imported files as well.'''
    assert isinstance(ast, list)
    assert isinstance(curdir, str)
    assert includepath is None or isinstance(includepath, list)
    if includepath is None:
        includepath = []

    processed = set()

    # We need to awkwardly walk the list as a while loop because we are
    # potentially going to modify it (and its length).
    sz = len(ast)
    i = 0
    while i != sz:
        if isinstance(ast[i], AST.Import):
            # We found something we need to resolve.
            filename = ast[i].source
            s = None
            name = None
            if ast[i].relative:
                # The import should be resolved relative to the current
                # directory.
                name = os.path.join(curdir, filename)
                processed.add(name)
                if os.path.exists(name):
                    s = open(name, 'r').read()
            else:
                # The import should be resolved in the built-in context.
                for prefix in includepath:
                    name = os.path.join(prefix, filename)
                    if os.path.exists(name):
                        processed.add(name)
                        s = open(name, 'r').read()
                        break
            if s is None:
                raise Exception('Import \'%s\' could not be resolved' % filename)
            # At this point we have valid data 's' and can parse it into an AST
            included = parse_to_ast(s, cpp, cpp_flags, optimise)
            assign_filenames(included, name)
            # It's possible this imported data imported some other files as
            # well, in which case they need to be recursively resolved.
            included, proc = resolve_imports(included, \
                os.path.dirname(name), includepath, cpp, cpp_flags, optimise)
            processed.update(proc)
            # Now to insert the include objects at this point in the AST.
            ast[i:i+1] = included
            i += len(included) # Skip what has already been resolved
            sz = len(ast) # Update the loop termination condition that has changed
        else:
            i += 1
    return (ast, processed)

def dedupe(ast):
    '''Remove duplicates from a list of AST objects. If you run this after
    resolving references you risk deleting objects that are referenced.'''
    a = []
    for i in ast:
        if i not in a:
            a.append(i)
    return a

def collapse_references(ast):
    map(lambda x: x.collapse_references(), ast)
