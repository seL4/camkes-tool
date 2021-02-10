#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

set(CAMKES_TOOL_DIR "${CMAKE_CURRENT_LIST_DIR}" CACHE STRING "")
mark_as_advanced(CAMKES_TOOL_DIR)

option(CAmkESNoFPUByDefault "Set compilation flags to not use FPU. This is
    currently only supported on x86 but other architectures may be added." OFF)
mark_as_advanced(CAmkESNoFPUByDefault)

macro(camkes_tool_import_libraries)
    add_subdirectory(${CAMKES_TOOL_DIR} camkes-tool)
endmacro()

macro(camkes_tool_setup_camkes_build_environment)
    find_package(seL4 REQUIRED)
    find_package(elfloader-tool REQUIRED)
    find_package(musllibc REQUIRED)
    find_package(util_libs REQUIRED)
    find_package(seL4_libs REQUIRED)
    find_package(projects_libs REQUIRED)
    find_package(capdl REQUIRED)
    # Other project settings needed for static allocation.
    # This is done early on so that it works for projects loaded before
    # options processing in camkes-tool (notably, elfloader-tool).
    if(CAmkESCapDLStaticAlloc)
        # Need to compile the capDL loader for static alloc
        SetCapDLLoaderStaticAlloc()
        # Need to place the capDL loader ELF at the end of memory
        SetElfloaderRootserversLast()
    endif()

    sel4_import_kernel()
    elfloader_import_project()

    include(${CAMKES_TOOL_DIR}/camkes.cmake)
    # This sets up environment build flags and imports musllibc and runtime libraries.
    config_set(LibSel4MuslcSysConstructorPriority LIB_SEL4_MUSLC_SYS_CONSTRUCTOR_PRIORITY 201)
    musllibc_setup_build_environment_with_sel4runtime()
    if(CAmkESNoFPUByDefault)
        if(KernelArchX86)
            add_compile_options(-mno-sse -mgeneral-regs-only -mno-80387 -mno-fp-ret-in-387)
        endif()
    endif()
    sel4_import_libsel4()
    util_libs_import_libraries()
    sel4_libs_import_libraries()
    projects_libs_import_libraries()
    camkes_tool_import_libraries()
    capdl_import_project()

endmacro()

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(camkes-tool DEFAULT_MSG CAMKES_TOOL_DIR)
