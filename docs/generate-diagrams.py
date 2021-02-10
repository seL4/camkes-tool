#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#

'''Generate railroad diagrams of the CAmkES syntax. Note that this needs a very
up to date version of parcon to generate diagrams correctly. At time of writing,
you need to get this from https://github.com/javawizard/parcon.
'''

from __future__ import absolute_import, division, print_function, \
    unicode_literals

import os, sys

from parcon.railroad import Bullet, Loop, Nothing, Or, PRODUCTION, TEXT, Then, Token
from parcon.railroad.raildraw import draw_to_png

def Production(t):
    return Token(PRODUCTION, t)
def Text(t):
    return Token(TEXT, t)

def diag(*obj):
    o = list(obj) + [Bullet()]
    return Then(Bullet(), *o)

DIAGRAMS = [
    {'assembly':diag(
        Text('assembly'),
        Text('{'),
        Production('composition'),
        Or(Production('configuration'),
            Nothing()),
        Text('}'))
    },
    {'attribute':diag(
        Production('type'),
        Production('id'))
    },
    {'composition':diag(
        Text('composition'),
        Text('{'),
        Loop(Or(Production('instance'),
                Production('connection'),
                Nothing()),
            Nothing()),
        Text('}'))
    },
    {'component':diag(
        Text('component'),
        Production('id'),
        Text('{'),
        Loop(Or(
                Then(Text('control'), Text(';')),
                Then(Text('uses'), Production('id'), Production('id')),
                Then(Text('provides'), Production('id'), Production('id')),
                Then(Text('consumes'), Production('id'), Production('id')),
                Then(Text('emits'), Production('id'), Production('id')),
                Then(Text('dataport'), Production('id'), Production('id')),
                Then(Text('has'), Text('mutex'), Production('id')),
                Then(Text('has'), Text('semaphore'), Production('id')),
                Nothing()),
            Nothing()),
        Text('}'))
    },
    {'connection':diag(
        Text('connection'),
        Production('id'),
        Production('id'),
        Text('('),
        Text('from'),
        Production('id'),
        Text('.'),
        Production('id'),
        Text(','),
        Text('to'),
        Production('id'),
        Text('.'),
        Production('id'),
        Text(')'),
        Text(';'))
    },
    {'dataport':diag(
        Text('dataport'),
        Production('id'),
        Production('id'))
    },
    {'direction':diag(Or(
        Text('refin'),
        Text('in'),
        Text('inout'),
        Text('out')))
    },
    {'event':diag(
        Text('event'),
        Production('id'),
        Text('='),
        Production('number'))
    },
    {'instance':diag(
        Text('component'),
        Production('id'),
        Production('id'),
        Text(';'))
    },
    {'method':diag(
        Or(
            Text('void'),
            Production('type')),
        Production('id'),
        Text('('),
        Or(
            Text('void'),
            Loop(
                Production('parameter'),
                Nothing()),
            Nothing()),
        Text(')'),
        Text(';'))
    },
    {'parameter':diag(
        Production('direction'),
        Production('type'),
        Production('id'))
    },
    {'procedure':diag(
        Or(
            Loop(
                Production('method'),
                Nothing()),
            Nothing()))
    },
    {'setting':diag(
        Production('id'),
        Text('.'),
        Production('id'),
        Text('='),
        Or(Production('boolean'),
            Production('number'),
            Production('string'),
            Production('id')))
    },
    {'type':diag(Or(
        Text('int'),
        Text('integer'),
        Text('signed int'),
        Text('unsigned int'),
        Text('unsigned integer'),
        Text('int8_t'),
        Text('int16_t'),
        Text('int32_t'),
        Text('int64_t'),
        Text('uint8_t'),
        Text('uint16_t'),
        Text('uint32_t'),
        Text('uint64_t'),
        Text('real'),
        Text('double'),
        Text('float'),
        Text('uintptr_t'),
        Text('char'),
        Text('character'),
        Text('boolean'),
        Text('bool'),
        Text('string')))
    },
]

def main():
    if len(sys.argv) == 2:
        out = sys.argv[1]
    elif len(sys.argv) == 1:
        out = os.curdir
    else:
        sys.stderr.write('Usage: %s [output directory]\n' % sys.argv[0])
        return -1

    # Tweak options to hide the title we don't need.
    options = {
        'raildraw_title_hide':True,
        'raildraw_title_after':0,
    }

    # Dump each diagram as a PNG.
    for d in DIAGRAMS:
        path = os.path.join(out, '%s.png' % list(d.keys())[0])
        draw_to_png(d, options, path, True)

    return 0

if __name__ == '__main__':
    sys.exit(main())
