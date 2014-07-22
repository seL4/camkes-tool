#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

class Joiner(object):
    '''Useful thing for emitting lists and whatnot in templates. Look at the
    existing templates for some examples.'''

    def __init__(self, first, following):
        self.first = first
        self.following = following
        self.used = False

    def __repr__(self):
        if self.used:
            return self.following
        else:
            self.used = True
            return self.first
