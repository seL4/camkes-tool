/*#
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 #*/

/*- macro parse_dtb_node_reg(node) -*/
    /*- set regs = node.get('reg') -*/
    /*- set reg_set = [] -*/
    /*- if regs is not none -*/
        /*- if node.get('this_size_cells')[0] == 0 -*/
            /*? raise(TemplateError('This hardware device has a value of 0 for #size-cells, we do not support mapping in a block of 0 bytes')) ?*/
        /*- endif -*/

        /*- set num_address_cells = node.get('this_address_cells')[0] -*/
        /*- set num_size_cells = node.get('this_size_cells')[0] -*/

        /*- set reg_entry_size = num_address_cells + num_size_cells -*/
        /*- set num_regs = len(regs) // reg_entry_size -*/
        /*- for i in range(0, num_regs) -*/

            /*- set index = i -*/

            /*# Set a temporary namespace to bypass scoping #*/
            /*- set temp_ns = namespace(paddr=0, size=0) -*/
            /*- for j in range(0, num_address_cells) -*/
                /*# Extract the paddr and size, read back to front, the register address and size #*/
                /*# is written in big endian, __rshift__ because Jinja2 doesn't like '<<' #*/
                /*- set paddr_part = regs[i * reg_entry_size + (num_address_cells - 1 - j)].__lshift__(j * 32) -*/
                /*- set temp_ns.paddr = temp_ns.paddr + paddr_part -*/
            /*- endfor -*/

            /*- for j in range(0, num_size_cells) -*/
                /*# Same idea as above #*/
                /*- set size_part = regs[i * reg_entry_size + (num_size_cells - 1 - j) + num_address_cells].__lshift__(j * 32) -*/
                /*- set temp_ns.size = temp_ns.size + size_part -*/
            /*- endfor -*/

            /*- set paddr =  macros.align_page_address(temp_ns.paddr, options.architecture) -*/
            /*- set size = temp_ns.size -*/

            /*- do reg_set.append((paddr, size)) -*/
        /*- endfor -*/
    /*- endif -*/
    /*- do stash('reg_set', reg_set) -*/
/*- endmacro -*/

/*- macro parse_dtb_node_interrupts(node, max_num_interrupts) -*/
    /*- set irq_set = macros.parse_dtb_node_interrupts(node, max_num_interrupts) -*/
    /*- do stash('irq_set', irq_set) -*/
/*- endmacro -*/
