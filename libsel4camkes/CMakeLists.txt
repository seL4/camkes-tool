#
# Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.7.2)

project(libsel4camkes C ASM)

set(configure_string "")

config_string(
    CAmkESDefaultHeapSize
    CAMKES_DEFAULT_HEAP_SIZE
    "Heap size to allocate per-component, in bytes."
    DEFAULT
    1048576
    UNQUOTE
)

config_choice(
    CAmkESErrorHandlingMode
    CAMKES_ERROR_HANDLING_MODE
    "Select the mode of error handling used in the glue code. It should only
    be necessary to adjust this setting if you are doing verification.
    Otherwise, the default error handling mechanism allows for
    configuration at runtime.

    Standard -> Standard error handling mechanism, that is configurable by the user at
    runtime. See the documentation for details of the API for this.

    Guards -> Use verification-visible guards at the site of each potential error.
    Note that this assumes that none of the error conditions are possible.
    If you are trying to verify code, you will be forced to prove that none
    of the error conditions can ever actually occur.

    Abort -> Call 'abort' inline when an error occurs. For debugging purposes, this
    is probably not the behaviour you want as it will give you no
    information about the error. The standard error handling mechanism has
    a nicer default for debugging. This mode is primarily useful when you
    want to verify code whose error handlers are unreachable for
    non-trivial reasons.

    Discard -> Perform the 'discard' action on any error that occurs. The advantage of
    this over simply configuring this behaviour via the standard mechanism
    is that you will not need to reason about any of the complicated error
    handling structures or control flow. This has no implementation
    advantages over the standard mechanism."
    "Standard;CAmkESErrorHandlingConfigurable;CAMKES_ERROR_HANDLER_CONFIGURABLE"
    "Guards;CAmkESErrorHandlingGuard;CAMKES_ERROR_HANDLER_GUARD"
    "Abort;CAmkESErrorHandlingAbort;CAMKES_ERROR_HANDLER_ABORT"
    "Discard;CAmkESErrorHandlingDiscard;CAMKES_ERROR_HANDLER_DISCARD"
)

config_option(
    CAmkESConnectorTiming
    CAMKES_CONNECTOR_TIMING
    "Enable timing points within connector templates that take cycle counter
    values as they are passed. This timing data can then be retrieved after
    execution."
    DEFAULT
    OFF
)

config_choice(
    CAmkESTLSModel
    CAMKES_TLS_MODEL
    "The CAmkES glue code uses thread-local variables for marshalling and
    unmarshalling of RPC parameters. This setting controls how this thread-
    local storage is implemented.

    standard -> Allocate thread-local variables on the stack or the heap as appropriate.
    This is the default and will hold the fewest surprises for C
    programmers.

    per-thread -> Allocate per-thread global variables for use as thread-local storage.
    The main purpose of this implementation is to avoid taking the address
    of local variables, an idiom that cannot be handled by the verification
    C parser."
    "standard;CAmkESTLSStandard;CAMKES_TLS_STANDARD"
    "per-thread;CAmkESTLSPerThreadGlobal;CAMKES_TLS_PTG"
)

add_config_library(sel4camkes "${configure_string}")

set(adjusted_seL4_arch "${KernelSel4Arch}")
if("${KernelSel4Arch}" STREQUAL "arm_hyp")
    set(adjusted_seL4_arch "aarch32")
endif()

file(
    GLOB
        deps
        src/*.c
        src/arch/${KernelArch}/*.c
        src/sel4_arch/${adjusted_seL4_arch}/*.c
        src/sel4_arch/${adjusted_seL4_arch}/gdb_server/*.c
        src/arch/${KernelArch}/*.S
        src/arch/${KernelArch}/*.c
        src/sel4_arch/${adjusted_seL4_arch}/*.S
)

list(SORT deps)

add_library(sel4camkes STATIC EXCLUDE_FROM_ALL ${deps})
target_include_directories(sel4camkes PUBLIC include)
target_include_directories(sel4camkes PRIVATE src/arch_include)
target_link_libraries(
    sel4camkes
    muslc
    sel4
    sel4debug
    platsupport
    sel4muslcsys
    sel4sync
    virtqueue
    sel4camkes_Config
    sel4runtime_Config
    sel4_autoconf
)
