/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*- if len(me.parent.from_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single from end are not supported', me.parent)) ?*/
/*- endif -*/

/*- set thy = os.path.splitext(os.path.basename(options.outfile.name))[0] -*/
header {* Event Send *}
(*<*)
theory /*? thy ?*/ imports
  "~~/../l4v/tools/c-parser/CTranslation"
  "~~/../l4v/tools/autocorres/AutoCorres"
  "~~/../l4v/tools/autocorres/NonDetMonadEx"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/glue-proofs.
 *)

declare [[allow_underscore_idents=true]]

install_C_file "/*? thy ?*/_seL4AsynchNative_pruned.c_pp"

autocorres [ts_rules = nondet] "/*? thy ?*/_seL4AsynchNative_pruned.c_pp"

locale /*? thy ?*/_seL4AsynchNative_glue = /*? thy ?*/_seL4AsynchNative_pruned
begin

lemma /*? me.interface.name ?*/__run_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> /*? me.interface.name ?*/__run' \<lbrace>P\<rbrace>!"
  apply (unfold /*? me.interface.name ?*/__run'_def)
  apply wp
  apply simp
  done

lemma seL4_Notify_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace>
    seL4_Notify' cap data
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Notify'_def seL4_MessageInfo_new'_def)
  apply wp
  apply simp
  done
(*>*)

text {*
  The CAmkES glue code for the sending side of an event consists of a single function for emitting
  a single instance of that event. The generated code is as follows.
  \clisting{eventfrom-emit-underlying.c}

  The safety of this function is straightforward to show as follows.
*}
lemma /*? me.interface.name ?*/_emit_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> /*? me.interface.name ?*/_emit_underlying' \<lbrace>P\<rbrace>!"
  apply (simp add:/*? me.interface.name ?*/_emit_underlying'_def)
  apply (wp seL4_Notify_wp)
  apply simp
  done

(*<*)
end

end
(*>*)
