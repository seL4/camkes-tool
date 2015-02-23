/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/* Linker script for CAmkES components. */
ENTRY(_start)

SECTIONS {
    /* __executable_start is required by libsel4platsupport. */
    PROVIDE (__executable_start = 0x100000);
    . = 0x100000;

    /* Code. */
    .text : ALIGN(4096) {
        *(.text*)
    }

    /* Read Only Data. */
    .rodata : ALIGN(4096) {
        *(.rodata*)
    }

    /*- if arch == 'arm' -*/
    PROVIDE_HIDDEN (__exidx_start = .);
    .ARM.exidx   : { *(.ARM.exidx* .gnu.linkonce.armexidx.*) }
    PROVIDE_HIDDEN (__exidx_end = .);
    /*- endif -*/

    /* Data / BSS */
    .data : ALIGN(4096) {
        *(.data)
    }

    .bss : {
        *(.bss)
        *(COMMON)
    }

    guarded (NOLOAD) : ALIGN(4096) {
	 *(guarded)
    }

    /*- for c in me.composition.connections -*/
    /*- if c.type.name == 'seL4SharedData' -*/
    shared_/*? c.from_interface.name ?*/ (NOLOAD) : ALIGN(0x1000000) {
        *(shared_/*? c.from_interface.name ?*/)
    }
    shared_/*? c.to_interface.name ?*/ (NOLOAD) : ALIGN(0x1000000) {
        *(shared_/*? c.to_interface.name ?*/)
    }
    /*- endif -*/
    /*- endfor -*/

    persistent (NOLOAD) : ALIGN(0x1000000) {
	 *(persistent)
    }

    /*- for c in me.composition.connections -*/
    /*- if c.type.name == 'seL4HardwareMMIO' -*/
    /*- if arch == 'arm' -*/
    ignore_/*? c.from_interface.name ?*/ (NOLOAD) : ALIGN(0x100000) { /*# ARM Section Size #*/
    /*- else -*/
    ignore_/*? c.from_interface.name ?*/ (NOLOAD) : ALIGN(0x400000) { /*# IA32 4M Page Size #*/
    /*- endif -*/
        *(ignore_/*? c.from_interface.name ?*/)
    }
    /*- endif -*/
    /*- endfor -*/

    _end = .;
}
