/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/* Linker script for CAmkES components. */

/*- if options.architecture in ('x86_64') -*/
  /*- set align = '0x200000' -*/
/*- elif options.architecture in ('aarch32', 'arm_hyp') -*/
  /*- set align = '0x100000' -*/
/*- elif options.architecture in ('ia32') -*/
  /*- set align = '0x400000' -*/
/*- endif -*/

/*- set instances = composition.instances -*/
/*- set grouped = [False] -*/

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
INSERT AFTER .tbss
/*- endif -*/

SECTIONS {

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

        /*- for size in macros.page_sizes(options.architecture) -*/

            /*- set size_bits = int(math.log(size, 2)) -*/

            align_/*? size_bits ?*/bit (NOLOAD) : ALIGN(/*? size ?*/) {
                *(align_/*? size_bits ?*/bit)
            }

        /*- endfor -*/
    /*- endif -*/
}
INSERT AFTER .bss;
