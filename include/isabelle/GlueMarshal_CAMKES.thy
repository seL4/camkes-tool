(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory GlueMarshal_CAMKES imports
    CTranslation
    Lib_CAMKES
    "/home/matthew/l4.verified/auto-refine/ValidNoFail"
    "/home/matthew/l4.verified/auto-refine/AutoRefine" (*FIXME: Remove absolute path *)
begin

install_C_file "marshal.c_pp"
(* print_theorems *)

context marshal begin
local_setup {* AutoRefine.abstract "marshal.c_pp" *}
(* print_theorems *)
print_theorems

(* Dereference a pointer *)
abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"
abbreviation "byte_cast x \<equiv> ((ptr_coerce x)::8 word ptr)"

lemma memcpy_char:
  "\<lbrace> \<lambda>s. c_guard (x::8 word ptr) \<and>
         c_guard (y::8 word ptr) \<and>
         unat sz = size_of TYPE(8 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y\<rbrace>
      memcpy' (ptr_coerce y) (ptr_coerce x) sz
   \<lbrace>\<lambda> _ s. P (deref s y) \<rbrace>!"
  (* Evaluate sz *)
  apply (clarsimp simp:unat_eq_1(2))

  unfolding memcpy'_def apply clarsimp
  apply wp

  (* Unroll the loop twice *)
  apply (subst whileLoop_unfold', wp)
     apply (subst whileLoop_unfold', wp)

  (* The remaining loop is never encountered *)
       apply (rule validNF_false_pre)
      apply wp

  (* Finally we're left with the single assignment *)
  apply (clarsimp simp:ptr_add_0_id hrs_mem_update h_val_heap_update)
 done
    
lemma marshal_unmarshal_char:
  "\<lbrace> \<lambda>s. c_guard (x::8 word ptr) \<and>
         c_guard (y::8 word ptr) \<and>
         c_guard (buffer::8 word ptr) \<and>
         unat sz = size_of TYPE(8 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y  \<and>
         x \<noteq> buffer \<and>
         y \<noteq> buffer \<rbrace>
      do
        camkes_marshal' (ptr_coerce buffer) (ptr_coerce x) sz;
        camkes_unmarshal' (ptr_coerce buffer) (ptr_coerce y) sz
      od
   \<lbrace> \<lambda>_ s. P (deref s y) \<rbrace>!"
  unfolding camkes_marshal'_def camkes_unmarshal'_def
  apply (wp add:memcpy_char del:validNF_prop)
  apply clarsimp
 done

end

end
