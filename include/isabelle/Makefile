#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

default: marshal.c_pp

%.h_pp: ../camkes/%.h
	cpp $^ >$@

%.c_pp: ../src/%.c
	cpp -I../ $^ >$@

clean:
	rm -f marshal.c_pp
