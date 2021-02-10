#
# Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.7.2)

# This is expected to be the root CMakeLists file for a CAmkES based project and symlinked
# to the top level directory. Although it is also fine, and expected, that some systems
# may need to define their own root CMakeLists file. Hopefully the comments here provide
# enough guidance for how to do this.

project(camkes-application NONE)

include(settings.cmake)

# Include the base. As per the comment above, we expect to be in the root directory and
# so we do not need to declare a specific kernel directory
include("${CMAKE_CURRENT_LIST_DIR}/projects/seL4_tools/cmake-tool/base.cmake")

# Now define our CAmkES extensions
include("${CMAKE_CURRENT_LIST_DIR}/tools/camkes/camkes.cmake")

# Include all the other projects
add_subdirectory("${CMAKE_CURRENT_LIST_DIR}/tools/camkes/libsel4camkes")
add_subdirectory("${CMAKE_CURRENT_LIST_DIR}/tools/camkes/libcamkescakeml")
include("${CMAKE_CURRENT_LIST_DIR}/projects/seL4_tools/cmake-tool/projects.cmake")

# Should be done adding targets, can now generate the root server and the global configuration
GenerateCAmkESRootserver()
