(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Lib_CAMKES imports
    "/home/matthew/l4.verified/auto-refine/ValidNoFail"
    CTranslation
begin

(* Lemmas that belong somewhere else. If you are browsing this file and know
 * where a lemma should go, feel free to move it if you can do so without
 * breaking my proofs.
 *)

(* Adding 0 to a pointer leaves it unchanged *)
lemma ptr_add_0_id:"x +\<^isub>p 0 = x"
  by (case_tac x, simp)

(* All non-null byte pointers are well-formed *)
lemma byte_ptr_ok:"ptr_val (x::8 word ptr) \<noteq> 0 \<Longrightarrow> c_guard x"
  unfolding c_guard_def c_null_guard_def ptr_aligned_def
  by (clarsimp simp: intvl_Suc simp del:word_neq_0_conv)

lemma no_fail_false[wp]:"no_fail (\<lambda>s. False) f"
 by (clarsimp simp:no_fail_def)

lemma validNF_false_pre:"\<lbrace>\<lambda>_. False\<rbrace> a \<lbrace>P\<rbrace>!"
  apply rule
  apply (wp|simp)+
 done

end
