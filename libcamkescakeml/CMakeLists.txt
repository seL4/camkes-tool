#
# Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.7.2)

project(libcamkescakeml C)

add_library(camkescakeml STATIC EXCLUDE_FROM_ALL
    src/args.c src/io.c src/camkes_init.c src/exit.c src/ipc.c src/virtqueue.c)
target_link_libraries(camkescakeml muslc sel4camkes)
