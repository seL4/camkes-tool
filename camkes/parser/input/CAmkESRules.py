#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''CAmkES (ADL and/or IDL) top level starting token. See accompanying docs for
more information.'''

def p_camkes(t):
    '''camkes :
              | adl camkes
              | idl camkes'''
    if len(t) == 1:
        t[0] = []
    else:
        assert len(t) == 3
        t[0] = t[1] + t[2]
