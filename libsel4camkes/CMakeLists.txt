#
# Copyright 2018, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

cmake_minimum_required(VERSION 3.7.2)

project(libsel4camkes C ASM)

file(GLOB deps
    src/*.c
    src/arch/${KernelArch}/*.c
    src/sel4_arch/${KernelSel4Arch}/*.c
    src/sel4_arch/${KernelSel4Arch}/gdb_server/*.c
    src/arch/${KernelArch}/*.S
    src/sel4_arch/${KernelSel4Arch}/*.S
)

list(SORT deps)

add_library(sel4camkes STATIC EXCLUDE_FROM_ALL ${deps})
target_include_directories(sel4camkes PUBLIC include)
target_link_libraries(sel4camkes muslc sel4 platsupport Configuration sel4muslcsys)
