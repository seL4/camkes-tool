#
# Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.8.2)

DeclareCAmkESComponent(PIT)
DeclareCAmkESComponent(Serial)

if(LibPlatSupportX86ConsoleDeviceEGA)
    message("LibPlatSupportX86ConsoleDeviceEGA is on.")
elseif(LibPlatSupportX86ConsoleDevice)
    message("Serial port ${LibPlatSupportX86ConsoleDevice} selected.")
    CAmkESAddImportPath(
        ${CMAKE_CURRENT_LIST_DIR}/components/serial_${LibPlatSupportX86ConsoleDevice}/
    )
else()
    message("Automatically select com1 for serial port.")
    CAmkESAddImportPath(${CMAKE_CURRENT_LIST_DIR}/components/serial_com1)
endif()
