/*#
 *#Copyright 2019, Data61
 *#Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 *#ABN 41 687 119 230.
 *#
 *#This software may be distributed and modified according to the terms of
 *#the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *#See "LICENSE_BSD2.txt" for details.
 *#
 *#@TAG(DATA61_BSD)
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

/*- macro parse_dtb_node_interrupts(node, max_num_interrupts, architecture) -*/
    /*- set interrupts = node.get('interrupts') -*/
    /*- set irq_set = [] -*/
    /*- if 'riscv' in architecture -*/
    /*# This section assumes that the `interrupts` binding's format follows those of the #*/
    /*# SiFive PLIC, i.e cell 1 = Interrupt 1, cell 2 = Interrupt 2, cell N = Interrupt N #*/
    /*# number per cell #*/
        /*- if interrupts is not none -*/
            /*- set num_interrupts=len(interrupts) -*/
            /*- if max_num_interrupts != -1 and num_interrupts > max_num_interrupts -*/
                /*? raise(TemplateError('Device %s has more than %d interrupts, this is more than we can support.') % (me.interface.name, max_num_interrupts)) ?*/
            /*- endif -*/
            /*- for i in range(0, num_interrupts) -*/
                /*- set _irq = interrupts[i] -*/
                /*- do irq_set.append(_irq) -*/
            /*- endfor -*/
        /*- endif -*/
        /*- do stash('irq_set', irq_set) -*/
    /*- elif 'aarch' in architecture or 'arm' in architecture -*/
        /*# This section assumes that the `interrupts` binding's format follow those of the #*/
        /*# ARM GIC (not v3), i.e. cell 1 = SPI, cell 2 = interrupt number and cell 3 the flag. #*/
        /*- set is_extended_interrupts = False -*/
        /*- if interrupts is none -*/
            /*- set interrupts = node.get('interrupts_extended') -*/
            /*- set is_extended_interrupts = True -*/
        /*- endif -*/
        /*- if interrupts is not none -*/
            /*- if is_extended_interrupts -*/
                /*- set num_interrupts = len(interrupts) // 4 -*/
            /*- else -*/
                /*- set num_interrupts = len(interrupts) // 3 -*/
            /*- endif -*/
            /*- if max_num_interrupts != -1 and num_interrupts > max_num_interrupts -*/
                /*? raise(TemplateError('Device %s has more than %d interrupts, this is more than we can support.') % (me.interface.name, max_num_interrupts)) ?*/
            /*- endif -*/

            /*- for i in range(0, num_interrupts) -*/
                /*- if is_extended_interrupts -*/
                    /*- set _irq = interrupts[i * 3 + 2] -*/
                    /*- set _irq_spi = interrupts[i * 3 + 1] -*/
                /*- else -*/
                    /*- set _irq = interrupts[i * 3 + 1] -*/
                    /*- set _irq_spi = interrupts[i * 3 + 0] -*/
                /*- endif -*/
                /*- if (isinstance(_irq_spi, numbers.Integral)) and (_irq_spi == 0) -*/
                    /*- set _irq = _irq + 32 -*/
                /*- endif -*/
                /*- do irq_set.append(_irq) -*/
            /*- endfor -*/
        /*- endif -*/
        /*- do stash('irq_set', irq_set) -*/
    /*- else -*/
        /*? raise(TemplateError('Device %s has unknown architecture %s') % (me.interface.name, architecture)) ?*/
    /*- endif -*/
/*- endmacro -*/
