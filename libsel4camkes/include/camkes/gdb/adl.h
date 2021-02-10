/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define DEBUG_COMPOSITION(TARGET, IRQ_NUM, IOPORT_RANGE) \
assembly {  \
    composition {   \
    component debug_server debug; \
    component debug_serial debug_hw_serial; \
    connection seL4HardwareIOPort debug_port (from debug.serial_port, to debug_hw_serial.serial); \
    connection seL4HardwareInterrupt interrupt1 (from debug_hw_serial.serial_irq, to debug.serial_irq); \
    connection seL4RPC delegate_con (from debug.delegate, to TARGET.delegate); \
    connection seL4GDB debug0 (from TARGET.fault, to debug.client_fault); \
    connection seL4GDBMem debug0_mem (from TARGET.GDB_mem, to TARGET.GDB_mem_handler); \
    } \
    configuration { \
        debug_hw_serial.serial_irq_irq_number = IRQ_NUM; \
        debug_hw_serial.serial_attributes = IOPORT_RANGE; \
        TARGET.debug = True; \
    } \
}

#define DEBUG_COMPONENT() \
  uses CAmkES_Debug fault; \
  provides GDB_delegate delegate; \
  uses CAmkES_Debug GDB_mem; \
  provides CAmkES_Debug GDB_mem_handler;
