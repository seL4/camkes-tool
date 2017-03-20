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

    .init : {
        KEEP (*(SORT_NONE(.init)));
    }

    /* Code. */
    .text : ALIGN(4096) {
        KEEP(*(preserved_text));
        *(.text*)
    }

    .fini : {
        KEEP (*(SORT_NONE(.fini)));
    }

    /* Read Only Data. */
    .rodata : ALIGN(4096) {
        *(.rodata*)
    }

    /*- if arch == 'aarch32' or arch == 'arm_hyp' -*/
    PROVIDE_HIDDEN (__exidx_start = .);
    .ARM.exidx   : { *(.ARM.exidx* .gnu.linkonce.armexidx.*) }
    PROVIDE_HIDDEN (__exidx_end = .);
    /*- endif -*/

    /* Data / BSS */
    .data : ALIGN(4096) {
        PROVIDE(__data_start = .);
        *(.data)
        PROVIDE(__data_end = .);
    }

    .bss : {
        PROVIDE(__bss_start = .);
        *(.bss)
        *(COMMON)
        PROVIDE(__bss_end = .);
    }

    guarded (NOLOAD) : ALIGN(4096) {
        KEEP(*(guarded))
    }

    /*- for c in composition.connections -*/
    /*- if c.type.name == 'seL4SharedData' -*/
      /*- if c.from_instance == me -*/
    shared_/*? c.from_interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
        *(shared_/*? c.from_interface.name ?*/)
    }
      /*- endif -*/
      /*- if c.to_instance == me -*/
    shared_/*? c.to_interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
        *(shared_/*? c.to_interface.name ?*/)
    }
      /*- endif -*/
    /*- endif -*/
    /*- endfor -*/

    persistent (NOLOAD) : ALIGN(0x1000) {
        *(persistent)
    }

    /*- for c in composition.connections -*/
    /*- if c.type.name == 'seL4HardwareMMIO' and c.from_instance == me -*/
    /*- if arch == 'aarch32' or arch == 'arm_hyp' -*/
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
