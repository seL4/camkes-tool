<!--
     Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# CAmkES Debug Manual

This document describes the structure and use of the CAmkES debug tool, which allows you to debug systems built on the CAmkES platform.
The [Usage](#usage) section describes how to debug a component built on CAmkES, as well as the current limitations of the tool.
The [Implementation](#implementation) section describes the internal implementation of the tool.
This document assumes some familiary with [CAmkES](https://github.com/seL4/camkes-tool/blob/master/docs/index.md) and the [seL4 microkernel](http://sel4.systems/).
If you are not familiar with them then you should read their documentation first.

A working example app, [debug-simple](https://github.com/seL4/camkes/tree/master/apps/debug-simple), can be found in the camkes sample apps project.

## Usage

This debug tool will provide an interface for you to debug components within CAmkES. Currently, the debug tool is only compatible with ia32.

Configuring a component for remote debugging the following is required:
 * Enable CAmkES preprocessing which is achieved by setting the CAMKES_CPP Kconfig setting.
 * Ensure that CAPDL_LOADER_WRITEABLE_PAGES is also set to allow GDB to rewrite instructions for software breakpoints.
 * Add `#include <camkes/gdb/adl.h>` which imports the DEBUG CPP macros used to easily modify existing components.
 * Add `DEBUG_COMPONENT()` to the definition of your component.  This creates connectors that the gdb server uses to modify the components state.
 * Add `DEBUG_COMPOSITION(client, 3, "0x2f8:0x2ff")` under your assembly section.  This adds additional assembly information that creates
the debug server and connects it to the serial hardware and your component to debug.  3 is the interrupt number of the serial port and "0x2f8:0x2ff"
refers to the hardware IOPort addresses.  If you are debugging on hardware with a single serial port, you will need to stop your application and the
kernel from using it for output.

### Example CAmkES file
```c
import <std_connector.camkes>;
#include <camkes/gdb/adl.h>
import "Simple.idl4";

component Client {
    control;
    uses Simple a;
    /* This adds the required connector interfaces for the debug server to use */
    DEBUG_COMPONENT()
}

component Echo {
    provides Simple b;
}

assembly {
    composition {
        component Echo echo;
        component Client client;
        connection seL4RPCCall simple(from client.a, to echo.b);
    }
}

/* This adds the assembly and configuration parts for the debug server to connect to `client`
   and specifies the serial port settings.
 */
DEBUG_COMPOSITION(client, 3, "0x2f8:0x2ff")
```


### Debugging
After you have built the image, you should be able to connect to the serial port via GDB.
The GDB connection will only be opened once there is a fault or breakpoint, so if you want
to inspect on startup you should set a code breakpoint within the component you are debugging.
This is achieved by using `camkes_software_breakpoint();` provided by `#include <camkes/debug.h>`

### Using GDB
Current functionality includes:
 * reading memory and registers, backtrace, seeing variables.
 * Writing memory and registers
 * Software and hardware breakpoints can be set.
 * Hardware watchpoints can be set on global variables.

### Using qemu

It's possible to debug a system running in qemu. To do this, one must forward the output of the second serial port to the tcp port gdb is connected to (1234 by default).
We provide a script that runs the current image in the "images" directory on qemu, forwarding the first serial port to the terminal where the script is running,
and the second serial port to 127.0.0.1:1234.

To debug with the script, run `tools/camkes/debug/debug_qeum` in one terminal, and run `gdb` in a second terminal, running both commands from the top level of this project.

```bash
qemu-system-i386 -nographic -m 512 -cpu Haswell \
    -kernel kernel-ia32-pc99 \
    -initrd capdl-loader-experimental-image-ia32-pc99 \
    -device isa-serial,chardev=ch0 \
    -device isa-serial,chardev=ch1 \
    -chardev file,path=/dev/tty,id=ch0 \
    -chardev socket,host=127.0.0.1,port=1234,id=ch1,server,wait
```

### Known issues / Limitations
 * Currently only compatible with ia32
 * Watch points are not supported on stack variables
 * Taking a backtrace should work the first time, but will crash the component, so that no more debugging can be done


## Implementation

The information below assumes you are familiar with the functionality of CAmkES.

### Architecture

To enable debugging, a debug server component is created that can communicate with a remote GDB client over serial using the GDB remote serial protocol.
Currently it communicates over serial by having exclusive access to the serial device.  Once a client attaches, the server interprets GDB commands from the
client and provides responses.  To achieve this the GDB server component is connected to the debug target component using a seL4GDB rpc connection.  This connection
allows the server to read and write memory and registers, as well as set hardware breakpoints and watchpoints.  Additionally the target thread's fault handler endpoints
are all set to an endpoint that the GDB server waits on.  When the target first faults, this results in seL4 sending a fault message to the GDB server, that then decodes this
message and sends the relevant serial packet to the remote GDB client.  The remote GDB client can then interract with the debug target.

### Relevant files

**include/builtin/gdb-delegate.camkes** - This defines the CAmkES ADL required to create the GDB components and connections.

**libsel4camkes/include/camkes/gdb/idl.h** - Contains the CPP macros for more easily modifying a CAmkES project for debugging.

**camkes/templates/component.debug.c** - Debug target implementation of the RPC interface for reading and writing, registers and memory.

**camkes/templates/seL4GDB-from.template.c** - Template for the fault ep on the component side. This should just be generating a cap, since it is set manually later.
**camkes/templates/seL4GDB-to.template.c** - Template code for the GDB server fault handler.  This decodes the fault type and uses the gdb server library code for handling.

**libsel4camkes/src/gdb_server/[gdb.c|serial.c]** - GDB server and serial implementation can be found here.
**libsel4camkes/include/camkes/gdb/[gdb.h|serial.h|delegate_types.h]** - Header files for GDB server and serial interfaces.

**camkes/templates/[seL4GDBMem-to.template.c|seL4GDBMem-from.template.c]** - Template code for a fault handler to check if memory is readable or writeable on the debug target.


