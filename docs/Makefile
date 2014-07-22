#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

SOURCES=$(wildcard *.md)

ifeq (${V},1)
Q :=
else
Q:= @
endif

default: $(SOURCES:%.md=%.html) contents.js

%.html: %.md
	@echo " [MARKDOWN] $@"
	${Q}which markdown >/dev/null 2>/dev/null || { echo "markdown not found" ; exit 1 ; }
	${Q}{ echo "<html><head><meta http-equiv=\"Content-type\" content=\"text/html; charset=utf-8\" /></head><body>" ; sed -e 's/^\(#\+\) \(.*\)$$/\1 <a id="\2"><\/a>\2/g' $^ | markdown - ; echo "</body></html>" ; } >$@

contents.js: index.md
	@echo " [GEN] $@"
	${Q}grep '^#' $^ | sed -e 's/#/\&nbsp;\&nbsp;\&nbsp;\&nbsp;\&nbsp;/g' -e 's/^\(\(\&nbsp;\)\+\) \(.*\)$$/document.write("\1<a href=\\"#\3\\">\3<\/a><br\/>");/g' >$@

clean:
	@echo " [CLEAN] $(SOURCES:%.md=%.html) contents.js"
	${Q}rm -rf $(SOURCES:%.md=%.html)
	${Q}rm -rf contents.js
