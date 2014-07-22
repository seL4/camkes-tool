#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''ADL-relevant lexing tokens. See accompanying docs for more information.'''

keywords = set([
    'import',
    'assembly',
    'connector',
    'template',

    # Assembly context keywords
    'composition',
    'configuration',

    # Composition context keywords
    'connection',
    'component',
    'from',
    'to',
    'group',

    # Component context keywords
    'include',
    'control',
    'hardware',
    'provides',
    'uses',
    'emits',
    'consumes',
    'dataport',
    'maybe',
    'attribute',
    'has',
    'mutex',
    'semaphore',

    # Connector end types
    'Procedure',
    'Event',
    'Dataport',
    'Interface',
])
