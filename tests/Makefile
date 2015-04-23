#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

ifeq (${PYTHONPATH},)
  export PYTHONPATH:=$(abspath ..)
else
  export PYTHONPATH:=${PYTHONPATH}:$(abspath ..)
endif
PARSER?=camkes.parser

SHELL="/bin/bash"

ifeq (${V},1)
Q :=
else
Q := @
endif

define get_tests
$(sort $(wildcard *.${1}))
endef
CAMKES_TESTS=$(call get_tests,camkes)

EXPLICIT_TESTS=$(patsubst ./%,%,$(shell find . -type f -executable))

.PHONY: default
default: explicit generic

.PHONY: explicit
explicit: $(EXPLICIT_TESTS:%=explicit_%)

.PHONY: generic
generic: $(CAMKES_TESTS:%=generic_%)

.PHONY: help
help:
	@echo "Usage:                                                                 "
	@echo " make                             Run all tests                        "
	@echo " make explicit                    Run all explicit tests               "
	@echo " make explicit_foo.sh             Run explicit test foo.sh             "
	@echo " make generic                     Run all generic tests                "
	@echo " make generic_my-test.camkes    Run generic tests on my-test.camkes    "

explicit_%: %
	@echo " [EXEC] $^"
	${Q}PARSER=${PARSER} ./$^ 2>&1 | while read line; do echo "  [$^] $${line}"; done; exit $${PIPESTATUS[0]}

define toupper
$(shell echo "${1}" | tr '[:lower:]' '[:upper:]')
endef

define stable
@echo " [STABLE] ${1}"
${Q}python -m ${PARSER} "--file=${1}" --quiet >.stable1
${Q}python -m ${PARSER} --file=.stable1 --quiet >.stable2
${Q}diff -w .stable1 .stable2 &>/dev/null
${Q}rm -f .stable1 .stable2
endef

generic_%: %
	$(call stable,$^)
