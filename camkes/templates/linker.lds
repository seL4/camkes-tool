/*#
 *# Copyright 2015, NICTA
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

    /*- if options.architecture in ('aarch32', 'arm_hyp') -*/
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

    /*- for c in composition.connections -*/
      /*- if c.type.name == 'seL4SharedData' -*/
        /*- for index, e in enumerate(c.from_ends) -*/
          /*- if e.instance == me -*/
            shared_from_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
              *(shared_from_/*? index ?*/_/*? e.interface.name ?*/)
            }
          /*- endif -*/
        /*- endfor -*/
        /*- for index, e in enumerate(c.to_ends) -*/
          /*- if e.instance == me -*/
            shared_to_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
              *(shared_to_/*? index ?*/_/*? e.interface.name ?*/)
            }
          /*- endif -*/
        /*- endfor -*/
      /*- endif -*/
    /*- endfor -*/

    persistent (NOLOAD) : ALIGN(0x1000) {
        *(persistent)
    }

    /*- for c in composition.connections -*/
      /*- if c.type.name == 'seL4HardwareMMIO' -*/
        /*- for index, e in enumerate(c.from_ends) -*/
          /*- if e.instance == me -*/
            /*- if options.architecture in ('aarch32', 'arm_hyp') -*/
              ignore_from_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x100000) { /*# ARM Section Size #*/
            /*- else -*/
              ignore_from_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x400000) { /*# IA32 4M Page Size #*/
            /*- endif -*/
                *(ignore_from_/*? index ?*/_/*? e.interface.name ?*/)
              }
          /*- endif -*/
        /*- endfor -*/
      /*- endif -*/
    /*- endfor -*/

    _end = .;
}
