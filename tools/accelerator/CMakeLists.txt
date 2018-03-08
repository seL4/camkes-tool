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

# Build system for the CAmkES accelerator.

cmake_minimum_required (VERSION 3.7.2)
project (camkes-accelerator C)

find_program(xxd xxd)

find_library (CRYPTO crypto)
find_library (CUNIT cunit)
find_library (OPENSSL ssl)
find_library (SQLITE sqlite3)

set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -W -Wall -Wextra -std=gnu11")

if (NOT CMAKE_BUILD_TYPE)
  set (CMAKE_BUILD_TYPE Release)
endif (NOT CMAKE_BUILD_TYPE)
if (CMAKE_BUILD_TYPE MATCHES Debug)
  set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -DDEBUG")
endif (CMAKE_BUILD_TYPE MATCHES Debug)

# The accelerator itself.

add_executable (camkes-accelerator accelerator.c
    ${CMAKE_CURRENT_BINARY_DIR}/include/select_inputs.h
    ${CMAKE_CURRENT_BINARY_DIR}/include/select_output.h
    ${CMAKE_CURRENT_BINARY_DIR}/include/version.h)

file (MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include)
include_directories (${CMAKE_BINARY_DIR}/include)

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/include/select_inputs.h
    COMMAND cd "${CMAKE_CURRENT_SOURCE_DIR}/../../camkes/internal" && ${xxd} -include select_inputs.sql >"${CMAKE_CURRENT_BINARY_DIR}/include/select_inputs.h"
    DEPENDS ../../camkes/internal/select_inputs.sql)

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/include/select_output.h
    COMMAND cd "${CMAKE_CURRENT_SOURCE_DIR}/../../camkes/internal" && ${xxd} -i select_output.sql >"${CMAKE_CURRENT_BINARY_DIR}/include/select_output.h"
    DEPENDS ../../camkes/internal/select_output.sql)

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/include/version.h
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/version.h.d
    # Build a valid dependency file from the print-deps script, this is a little awkward
    COMMAND echo "include/version.h: " > "${CMAKE_CURRENT_BINARY_DIR}/version.h.d"
    COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/print-deps.py" >> "${CMAKE_CURRENT_BINARY_DIR}/version.h.d"
    COMMAND sed -i "s/$$/\\/" "${CMAKE_CURRENT_BINARY_DIR}/version.h.d"
    COMMAND
    COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/mkversion.py" >"${CMAKE_CURRENT_BINARY_DIR}/include/version.h"
    DEPENDS mkversion.py
    DEPENDS print-deps.py
    DEPFILE ${CMAKE_CURRENT_BINARY_DIR}/version.h.d
    )

target_link_libraries (camkes-accelerator ${CRYPTO} ${OPENSSL} ${SQLITE})

# Accelerator unit tests.

add_executable (camkes-accelerator-unittests EXCLUDE_FROM_ALL unittests.c
    ${CMAKE_CURRENT_BINARY_DIR}/include/select_inputs.h
    ${CMAKE_CURRENT_BINARY_DIR}/include/select_output.h
    ${CMAKE_CURRENT_BINARY_DIR}/include/version.h
    )

target_link_libraries (camkes-accelerator-unittests ${CRYPTO} ${CUNIT} ${OPENSSL} ${SQLITE})

enable_testing ()
add_test (unittests ${CMAKE_CURRENT_BINARY_DIR}/camkes-accelerator-unittests)

# Rules to install the accelerator executable
install(TARGETS camkes-accelerator
    RUNTIME DESTINATION bin
)
