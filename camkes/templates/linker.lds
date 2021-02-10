/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Linker script for CAmkES components. */

/*- set instances = composition.instances -*/
/*- set grouped = [False] -*/
/*- set rump = configuration[me.name].get('rump_config', False) -*/

/*# For single address space components we need to collect constructors
 *# and destructors early in order to prevent them from being called
 *# multiple times by each component.
 #*/
/*- for inst in instances if not me.type.hardware -*/
  /*- if id(me) != id(inst) and inst.address_space == me.address_space -*/
    /*- do grouped.__setitem__(0, True) -*/
  /*- endif -*/
/*- endfor -*/
/*- if grouped[0] -*/

SECTIONS {
    .init_array : {
        PROVIDE_HIDDEN (__init_array_start = .);
        KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*) SORT_BY_INIT_PRIORITY(.ctors.*)))
        KEEP (*(.init_array EXCLUDE_FILE (*crtbegin.o *crtbegin?.o *crtend.o *crtend?.o ) .ctors))
        PROVIDE_HIDDEN (__init_array_end = .);
    }

    .fini_array : {
        PROVIDE_HIDDEN (__fini_array_start = .);
        KEEP (*(SORT_BY_INIT_PRIORITY(.fini_array.*) SORT_BY_INIT_PRIORITY(.dtors.*)))
        KEEP (*(.fini_array EXCLUDE_FILE (*crtbegin.o *crtbegin?.o *crtend.o *crtend?.o ) .dtors))
        PROVIDE_HIDDEN (__fini_array_end = .);
    }

}
INSERT AFTER .bss
/*- endif -*/

SECTIONS {


  /*- for size in macros.page_sizes(options.architecture) -*/

      /*- set size_bits = int(math.log(size, 2)) -*/

      align_/*? size_bits ?*/bit (NOLOAD) : ALIGN(/*? size ?*/) {
          KEEP (*(align_/*? size_bits ?*/bit))
      }

  /*- endfor -*/
}
INSERT AFTER .bss;
/*- if not grouped[0] and not rump -*/
SECTIONS {
    .tdata :
    {
        _tdata_start = . ;
        *(.tdata .tdata.* .gnu.linkonce.td.*)
        _tdata_end = . ;
    }
    .tbss :
    {
        _tbss_start = . ;
        *(.tbss .tbss.* .gnu.linkonce.tb.*) *(.tcommon)
        _tbss_end = . ;
    }
}
INSERT AFTER .rodata;
/*- endif -*/
