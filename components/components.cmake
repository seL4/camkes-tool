#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# import all available components
CAmkESAddImportPath(${CMAKE_CURRENT_LIST_DIR})

CAmkESMaybeAddImportPath(
    ${CMAKE_CURRENT_LIST_DIR}/plat/${KernelPlatform} ${CMAKE_CURRENT_LIST_DIR}/mach/${KernelArmMach}
    ${CMAKE_CURRENT_LIST_DIR}/arch/${KernelArch}
)

include(${CMAKE_CURRENT_LIST_DIR}/plat/${KernelPlatform}/CMakeLists.txt OPTIONAL)
