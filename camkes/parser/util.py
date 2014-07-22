#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import sys

def get_tokens(context):
    '''
    Deduces a list of tokens to be used to build a lexer. These need to be
    present in the 'tokens' list when the lexer is built, but they can be
    automatically deduced from the t_* symbols and reserved keywords that are
    in scope in a given context.
    '''
    return map(lambda x: x[2:], \
              filter(lambda x: x.startswith('t_') and \
                               x not in ['t_ignore', 't_error'], context)) \
           + list(keywords)

# Reserved keywords. This global is intended to be
# referenced from several other files.
keywords = set()

def merge_keywords(more_keywords):
    '''Merge more keywords into the global list of reserved words.'''
    global keywords
    keywords = keywords.union(more_keywords)

def reset_keywords():
    '''Clear the list of reserved keywords.'''
    global keywords
    keywords = set()

def parse_error(message):
    print >>sys.stderr, 'Parsing error: %s' % message
    raise SyntaxError(message)
