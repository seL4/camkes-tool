#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

CAmkESAddTemplatesPath(.)

# Declare connectors with templates.
# We can rely on the naming scheme being consistent to allow for easier declaration.
foreach(
    connector
    IN
    ITEMS
    seL4DirectCall
    seL4GDB
    seL4GDBMem
    seL4Notification
    seL4NotificationBind
    seL4NotificationNative
    seL4NotificationQueue
    seL4RPCCall
    seL4DTBHardware
    seL4InitHardware
)
    DeclareCAmkESConnector(
        ${connector}
        FROM
        ${connector}-from.template.c
        TO
        ${connector}-to.template.c
    )
endforeach()
DeclareCAmkESConnector(
    seL4RPCCallNoType
    FROM
    seL4RPCCall-from.template.c
    TO
    seL4RPCCall-to.template.c
    CAKEML_TO
    seL4RPCCall-to.template.cakeml
)
DeclareCAmkESConnector(seL4RPCCall CAKEML_TO seL4RPCCall-to.template.cakeml)
DeclareCAmkESConnector(seL4SharedData FROM seL4SharedData.template.c TO seL4SharedData.template.c)
DeclareCAmkESConnector(seL4DMASharedData FROM seL4DMASharedData.template.c TO seL4DMASharedData.template.c)
# Connectors with only FROM end interfaces
foreach(connector IN ITEMS seL4HardwareMMIO seL4HardwareIOPort)
    DeclareCAmkESConnector(${connector} FROM ${connector}.template.c)
endforeach()
DeclareCAmkESConnector(seL4DTBHW TO seL4DTBHardware-to.template.c)
# Connectors with only TO end interfaces
foreach(connector IN ITEMS seL4HardwareInterrupt seL4IOAPICHardwareInterrupt)
    DeclareCAmkESConnector(${connector} TO ${connector}.template.c)
endforeach()
