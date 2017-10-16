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

# This is expected to be the root CMakeLists file for a CAmkES based project and symlinked
# to the top level directory. Although it is also fine, and expected, that some systems
# may need to define their own root CMakeLists file. Hopefully the comments here provide
# enough guidance for how to do this.

# First include the base. As per the comment above, we expect to be in the root directory and
# so we do not need to declare a specific kernel directory
include("${CMAKE_CURRENT_LIST_DIR}/projects/seL4_tools/cmake-tool/base.cmake")

# Now define our CAmkES extensions
include("${CMAKE_CURRENT_LIST_DIR}/tools/camkes/camkes.cmake")

# Define CapDL pieces. These do *not* get included when we define the rest of the projects
# as we want to include them here as they define additional variables and helpers we need
add_subdirectory("${CMAKE_CURRENT_LIST_DIR}/projects/capdl/capdl-loader-app")

# Include all the other projects
add_subdirectory("${CMAKE_CURRENT_LIST_DIR}/tools/camkes/libsel4camkes")
include("${CMAKE_CURRENT_LIST_DIR}/projects/seL4_tools/cmake-tool/projects.cmake")

# Should be done adding targets, can now generate the root server and the global configuration
GenerateCAmkESRootserver()

include("${CMAKE_CURRENT_LIST_DIR}/projects/seL4_tools/cmake-tool/configuration.cmake")
