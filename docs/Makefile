#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

ifeq (${V},1)
Q :=
else
Q:= @
endif

default: index.html camkes-manual.pdf

index.html: index.md
	@echo " [PANDOC] $@"
	${Q}pandoc -s --toc -o $@ $<

camkes-manual.pdf: index.md imgs/echo.png
	@echo " [PANDOC] $@"
	${Q}pandoc -s --toc -o $@ $<

clean:
	@echo " [CLEAN] index.html camkes-manual.pdf"
	${Q}rm -rf index.html camkes-manual.pdf
