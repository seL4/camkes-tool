/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/*- macro for_all_method_types(methods) -*/
    /*- set checked_types = set() -*/
    /*- for m in methods -*/
        /*- if m.return_type is not none and m.return_type not in checked_types -*/
            /*? caller(m.name, 'return', macros.show_type(m.return_type)) ?*/
            /*- do checked_types.add(m.return_type) -*/
        /*- endif -*/
        /*- for p in m.parameters -*/
            /*- if p.type not in checked_types -*/
                /*? caller(m.name, p.name, macros.show_type(p.type)) ?*/
                /*- do checked_types.add(p.type) -*/
            /*- endif -*/
        /*- endfor -*/
    /*- endfor -*/
/*- endmacro -*/
