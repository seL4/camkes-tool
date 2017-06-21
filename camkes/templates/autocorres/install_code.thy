/*#
 *# Copyright 2017, Data61
 *# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 *# ABN 41 687 119 230.
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(DATA61_BSD)
 #*/

/*- if 'autocorres/install_code.thy' not in included -*/
/*- do included.add('autocorres/install_code.thy') -*/

declare [[allow_underscore_idents=true]]

/*# If we're repeatedly iterating over variations on this file (as is often the
 *# case during development), PolyML gradually eats up your memory eventually
 *# sending the system into swap death. These steps are a sort of 'hail Mary'
 *# to try and prevent this.
 #*/
/*- if options.verbosity >= 2 -*/
  ML {* PolyML.fullGC () *}
/*- endif -*/

/*# Note that we expect the variable 'thy' to be set here. #*/
install_C_file "/*? thy ?*/_pruned.c_pp"

/*- if options.verbosity >= 2 -*/
  ML {* PolyML.fullGC () *}
/*- endif -*/

autocorres [ts_rules = nondet, skip_word_abs] "/*? thy ?*/_pruned.c_pp"

/*- if options.verbosity >= 2 -*/
  ML {* PolyML.fullGC () *}
/*- endif -*/

context "/*? thy ?*/_pruned" begin

/*- include 'autocorres/abort.thy' -*/
/*- include 'autocorres/inv.thy' -*/
/*- include 'autocorres/seL4_GetIPCBuffer_wp.thy' -*/
/*- include 'autocorres/camkes_get_tls_wp.thy' -*/
/*- include 'autocorres/getmr_setmr.thy' -*/
/*- include 'autocorres/packed.thy' -*/
/*- include 'autocorres/ptr.thy' -*/
/*- include 'autocorres/heap.thy' -*/
/*- include 'autocorres/tls_wps.thy' -*/

end

/*- endif -*/
