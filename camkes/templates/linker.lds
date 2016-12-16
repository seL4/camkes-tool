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

/*- if options.architecture in ('x86_64') -*/
  /*- set align = '0x200000' -*/
  /*- set start = align -*/
/*- elif options.architecture in ('aarch32', 'arm_hyp') -*/
  /*- set align = '0x100000' -*/
  /*- set start = align -*/
/*- elif options.architecture in ('ia32') -*/
  /*- set align = '0x400000' -*/
  /*- set start = '0x100000' -*/
/*- endif -*/

SECTIONS {
    /* __executable_start is required by libsel4platsupport. */

    PROVIDE (__executable_start = /*? start ?*/);
    . = /*? start ?*/;

    /* Code. */
    PROVIDE_HIDDEN (__text_start = .);
    .text : ALIGN(4096) {
        *(.text*)
    }
    PROVIDE_HIDDEN (__text_end = .);

    /* Read Only Data. */
    PROVIDE_HIDDEN (__rodata_start = .);
    .rodata : ALIGN(4096) {
        *(.rodata*)
    }
    PROVIDE_HIDDEN (__rodata_end = .);

    /*- if options.architecture in ('aarch32', 'arm_hyp') -*/
    PROVIDE_HIDDEN (__exidx_start = .);
    .ARM.exidx   : { *(.ARM.exidx* .gnu.linkonce.armexidx.*) }
    PROVIDE_HIDDEN (__exidx_end = .);
    /*- endif -*/

    /* Data / BSS */
    PROVIDE_HIDDEN (__data_start = .);
    .data : ALIGN(4096) {
        *(.data)
    }
    PROVIDE_HIDDEN (__data_end = .);

    PROVIDE_HIDDEN (__bss_start = .);
    .bss : {
        *(.bss)
        *(COMMON)
    }
    PROVIDE_HIDDEN (__bss_end = .);

    guarded (NOLOAD) : ALIGN(4096) {
        *(guarded)
    }

    /*- for c in composition.connections -*/
      /*- if c.type.name == 'seL4SharedData' -*/
        /*- for index, e in enumerate(c.from_ends) -*/
          /*- if id(e.instance) == id(me) -*/
            shared_from_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
              *(shared_from_/*? index ?*/_/*? e.interface.name ?*/)
            }
          /*- endif -*/
        /*- endfor -*/
        /*- for index, e in enumerate(c.to_ends) -*/
          /*- if id(e.instance) == id(me) -*/
            shared_to_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(0x1000) {
              *(shared_to_/*? index ?*/_/*? e.interface.name ?*/)
            }
          /*- endif -*/
        /*- endfor -*/
      /*- endif -*/
    /*- endfor -*/

    /*- for c in composition.connections -*/
      /*- if c.type.name == 'seL4HardwareMMIO' -*/
        /*- for index, e in enumerate(c.from_ends) -*/
          /*- if id(e.instance) == id(me) -*/
            ignore_from_/*? index ?*/_/*? e.interface.name ?*/ (NOLOAD) : ALIGN(/*? align ?*/) {
              *(ignore_from_/*? index ?*/_/*? e.interface.name ?*/)
            }
          /*- endif -*/
        /*- endfor -*/
      /*- endif -*/
    /*- endfor -*/

    /*- if options.architecture in ('aarch32', 'arm_hyp') -*/
    /* The ARM GNU Assembler does not permit allignment constraints of more than
     * 15 bits. To work around this limitation, objects which are multiples of
     * page sizes that require page-size-alignment are placed in sections aligned
     * to the size of a page. A section for 12-bit-aligned regular pages is
     * included for consistency.
     */
        align_12bit (NOLOAD) : ALIGN(0x1000) {
            *(align_12bit)
        }
        align_16bit (NOLOAD) : ALIGN(0x10000) {
            *(align_16bit)
        }
        align_20bit (NOLOAD) : ALIGN(0x100000) {
            *(align_20bit)
        }
        align_24bit (NOLOAD) : ALIGN(0x1000000) {
            *(align_24bit)
        }
    /*- endif -*/
    _end = .;
}
