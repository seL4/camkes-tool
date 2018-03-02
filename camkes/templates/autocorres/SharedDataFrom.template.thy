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

/*- if len(me.parent.from_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single from end are not supported', me.parent)) ?*/
/*- endif -*/

/*- set thy = me.interface.name -*/
header {* Shared Memory *}
(*<*)
theory "/*? thy ?*/" imports
  "~~/../l4v/tools/c-parser/CTranslation"
  "~~/../l4v/tools/autocorres/AutoCorres"
  "~~/../l4v/tools/autocorres/NonDetMonadEx"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/glue-proofs.
 *)

declare [[allow_underscore_idents=true]]

install_C_file "/*? thy ?*/_seL4SharedData_pruned.c_pp"

autocorres [ts_rules = nondet] "/*? thy ?*/_seL4SharedData_pruned.c_pp"

locale "/*? thy ?*/_seL4SharedData_glue" = "/*? thy ?*/_seL4SharedData_pruned"
begin
(*>*)

lemma /*? me.interface.name ?*/__run_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> /*? me.interface.name ?*/__run' \<lbrace>P\<rbrace>!"
  apply (unfold /*? me.interface.name ?*/__run'_def)
  apply wp
  apply simp
  done

lemma /*? me.interface.name ?*/_wrap_ptr_nf:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
        is_valid_dataport_ptr__C s x\<rbrace>
      /*? thy ?*/_wrap_ptr' x y
   \<lbrace>\<lambda>_ s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
                 is_valid_dataport_ptr__C s x\<rbrace>!"
  apply (unfold /*? me.interface.name ?*/_wrap_ptr'_def)
  apply wp
  apply simp
  done

/*- if False -*/ /*# Leave this out for now. #*/
(* Wrapping a valid dataport pointer returns success. XXX: You actually want to say more than this,
 * i.e. that the wrapper pointed is correct. Todo below.
 *)
lemma
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
        is_valid_dataport_ptr__C s x \<and>
        (ptr_val y) \<ge> (symbol_table ''/*? me.interface.name ?*/_data'') \<and>
        (ptr_val y) < (symbol_table ''/*? me.interface.name ?*/_data'') + /*? macros.sizeof(options.architecture, me.interface.type) ?*/\<rbrace>
        /*? me.interface.name ?*/_wrap_ptr' x y
   \<lbrace>\<lambda>r s. r = 0 \<and>
          (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
          is_valid_dataport_ptr__C s x \<and>
          (ptr_val y) \<ge> (symbol_table ''/*? me.interface.name ?*/_data'') \<and>
          (ptr_val y) < (symbol_table ''/*? me.interface.name ?*/_data'') + /*? macros.sizeof(options.architecture, me.interface.type) ?*/\<rbrace>!"
  apply (unfold /*? me.interface.name ?*/_wrap_ptr'_def)
  apply wp
  apply clarsimp
  apply unat_arith
  done
/*- endif -*/

lemma /*? me.interface.name ?*/_unwrap_ptr_nf:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
        is_valid_dataport_ptr__C s x\<rbrace>
     /*? me.interface.name ?*/_unwrap_ptr' x
   \<lbrace>\<lambda>_ s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''/*? me.interface.name ?*/_data'')) /*? macros.sizeof(options.architecture, me.interface.type) ?*/). is_valid_w8 s x) \<and>
          is_valid_dataport_ptr__C s x\<rbrace>!"
  apply (unfold /*? me.interface.name ?*/_unwrap_ptr'_def)
  apply wp
  apply simp
  done

(*<*)
end

end
(*>*)
