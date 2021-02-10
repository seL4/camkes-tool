(*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


structure camkesConstants = struct
/*# Attributes #*/
/*- set myconf = configuration[me.name] -*/
/*- for a in me.type.attributes -*/
    /*- set value = myconf.get(a.name) -*/
    /*- if value is not none -*/
        val /*? a.name ?*/ = "/*? value ?*/";
    /*- endif -*/
/*- endfor -*/

end
