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
