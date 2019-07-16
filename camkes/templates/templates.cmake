#
# Copyright 2019, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
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
    seL4RPC
    seL4RPCCall
    seL4RPCSimple
    seL4SharedData
    seL4DTBHardware
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
# Connectors with only FROM end interfaces
foreach(connector IN ITEMS seL4HardwareMMIO seL4HardwareIOPort)
    DeclareCAmkESConnector(${connector} FROM ${connector}.template.c)
endforeach()
# Connectors with only TO end interfaces
foreach(connector IN ITEMS seL4HardwareInterrupt seL4IOAPICHardwareInterrupt)
    DeclareCAmkESConnector(${connector} TO ${connector}.template.c)
endforeach()
