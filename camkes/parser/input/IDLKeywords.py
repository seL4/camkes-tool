#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''IDL-relevant lexing tokens. See accompanying docs for more information.'''

keywords = set([

    # Import statement
    'import',

    # Include a C file
    'include',

    # Interface start keyword
    'interface',
    'procedure',
    'event',

    # Parameter direction
    'in',
    'out',
    'inout',

    # Type decorator
    'unsigned',
    'signed',

    # Types
    'int',
    'integer',
    'int8_t',
    'int16_t',
    'int32_t',
    'int64_t',
    'uint8_t',
    'uint16_t',
    'uint32_t',
    'uint64_t',
    'real',
    'double',
    'float',
    'uintptr_t',
    'char',
    'character',
    'boolean',
    'bool',
    'string',
    'smallstring', # deprecated

    'void',
])
