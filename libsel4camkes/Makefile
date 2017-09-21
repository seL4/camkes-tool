#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

# Targets
TARGETS := libsel4camkes.a

# Source files required to build the target
CFILES := $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/*.c)) \
          $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/arch/${ARCH}/*.c)) \
          $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/sel4_arch/${SEL4_ARCH}/*.c)) \
          $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/sel4_arch/${SEL4_ARCH}/gdb_server/*.c))

ASMFILES := $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/arch/$(ARCH)/*.S))
ASMFILES += $(patsubst $(SOURCE_DIR)/%,%,$(wildcard ${SOURCE_DIR}/src/sel4_arch/$(SEL4_ARCH)/*.S))

# Header files/directories this library provides
HDRFILES := \
    $(wildcard ${SOURCE_DIR}/include/*)

NK_CFLAGS += -D_XOPEN_SOURCE=700

include $(SEL4_COMMON)/common.mk
