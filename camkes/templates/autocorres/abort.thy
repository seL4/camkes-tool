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

/*- if 'autocorres/abort.thy' not in included -*/
/*- do included.add('autocorres/abort.thy') -*/

(* Sanity check. If the definition of abort() is not included in the sources,
 * many of the other WP proofs become trivial. This proof will fail if we have
 * accidentally omitted abort().
 *)
lemma abort_wp[wp]:
  "\<lbrace>bottom\<rbrace> abort' \<lbrace>P\<rbrace>!"
  by (rule validNF_false_pre)

/*- endif -*/
