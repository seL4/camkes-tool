#
# Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
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
