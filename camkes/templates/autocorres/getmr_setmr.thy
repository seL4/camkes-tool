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

/*- if 'autocorres/getmr_setmr.thy' not in included -*/
/*- do included.add('autocorres/getmr_setmr.thy') -*/

/*- include 'autocorres/inv.thy' -*/
/*- include 'autocorres/seL4_GetIPCBuffer_wp.thy' -*/

(* We provide a more abstract monadic definition of seL4_SetMR than the
 * AutoCorres-generated version, to ease reasoning.
 *)
definition
  seL4_SetMR_lifted :: "sword32 \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> (unit \<times> lifted_globals) set \<times> bool"
where
  "seL4_SetMR_lifted i val \<equiv>
   do
     ret' \<leftarrow> seL4_GetIPCBuffer';
     guard (\<lambda>s. i <s seL4_MsgMaxLength);
     guard (\<lambda>s. 0 <=s i);
     modify (\<lambda>s. s \<lparr>heap_seL4_IPCBuffer__C :=
       (heap_seL4_IPCBuffer__C s)(ret' :=
          msg_C_update (\<lambda>a. Arrays.update a (unat i) val)
             (heap_seL4_IPCBuffer__C s ret'))
     \<rparr>)
  od"

(* Show that the abstracted version is actually equivalent to the
 * AutoCorres-generated version.
 *)
lemma lift_setmr:"ipc_buffer_valid s \<Longrightarrow> seL4_SetMR' i x s = seL4_SetMR_lifted i x s"
  apply (clarsimp simp:seL4_SetMR'_def seL4_SetMR_lifted_def)
  apply monad_eq
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=a in exI)
   apply (rule_tac x=b in exI)
   apply (simp cong: lifted_globals.fold_congs)
   apply (simp add:seL4_MsgMaxLength_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=a in exI)
   apply (rule_tac x=b in exI)
   apply (clarsimp simp:seL4_MsgMaxLength_def seL4_GetIPCBuffer'_def)
   apply monad_eq
   apply (simp add:inv_defs)
  apply (rule iffI)
   apply clarsimp
   apply (simp add:seL4_GetIPCBuffer'_def)
   apply monad_eq
   apply (erule disjE)
    apply force
   apply (clarsimp simp:ipc_buffer_valid_def ipc_buffer_ptr_def seL4_MsgMaxLength_def)+
  done

(* A version of the above lemma that is applicable in WP proofs. *)
lemma lift_setmr_hoare:
  "\<lbrakk>(\<forall>s. P s \<longrightarrow> ipc_buffer_valid s); \<lbrace>P\<rbrace> seL4_SetMR_lifted i x \<lbrace>Q\<rbrace>!\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> seL4_SetMR' i x \<lbrace>Q\<rbrace>!"
  apply (cut_tac P=P and P'=P and Q=Q and Q'=Q and m="seL4_SetMR' i x" and
                 m'="seL4_SetMR_lifted i x" in validNF_cong)
     apply simp
    apply (subst lift_setmr)
    apply clarsimp
   apply simp+
  done

(* Abstract functional definitions of seL4_SetMR and seL4_GetMR. *)
definition
  setMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMR s i v \<equiv>
      s\<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)
        (ipc_buffer_ptr s := msg_C_update (\<lambda>a. Arrays.update a i v) (ipc_buffer s))\<rparr>"
definition
  getMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32"
where
  "getMR s i \<equiv> index (msg_C (ipc_buffer s)) i"

(* Show refinement for seL4_SetMR. *)
lemma seL4_SetMR_wp[wp_unsafe]:
 "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        0 <=s i \<and>
        i <s seL4_MsgMaxLength \<and>
        (\<forall>x. P x (setMR s (unat i) v))\<rbrace>
     seL4_SetMR' i v
   \<lbrace>P\<rbrace>!"
  apply (subst lift_setmr_hoare)
    apply simp_all
  apply (simp add:seL4_SetMR_lifted_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:setMR_def inv_defs del:fun_upd_apply)
  done

(* Show refinement for seL4_GetMR. *)
lemma seL4_GetMR_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s.     0 <=s i \<and>
            i <s  seL4_MsgMaxLength \<and>
            globals_frame_intact s \<and>
            ipc_buffer_valid s \<and>
            P (getMR s (unat i)) s\<rbrace>
     seL4_GetMR' i
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_GetMR'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:getMR_def inv_defs seL4_MsgMaxLength_def)
  done

(* Some useful properties of the two functional representations. *)
lemma getMR_setMR:
  "\<lbrakk>i < nat (uint seL4_MsgMaxLength)\<rbrakk> \<Longrightarrow> getMR (setMR s j v) i = (if i = j then v else getMR s i)"
  apply (simp add:getMR_def setMR_def ipc_buffer_ptr_def ipc_buffer_def fun_upd_def seL4_MsgMaxLength_def)
  done

(* XXX: Would be nice for this to be generated for us. *)
lemma msg_update_id:"msg_C_update (\<lambda>r. Arrays.update r i (index (msg_C y) i)) y = y"
  apply (cut_tac f="(\<lambda>r. Arrays.update r i (index (msg_C y) i))" and
                 f'=id and r=y and r'=y in seL4_IPCBuffer__C_fold_congs(2))
     apply simp+
  apply (simp add:id_def)
  apply (metis seL4_IPCBuffer__C_accupd_diff(22) seL4_IPCBuffer__C_accupd_diff(24)
               seL4_IPCBuffer__C_accupd_diff(26) seL4_IPCBuffer__C_accupd_diff(28)
               seL4_IPCBuffer__C_accupd_diff(30) seL4_IPCBuffer__C_accupd_diff(41)
               seL4_IPCBuffer__C_accupd_same(2) seL4_IPCBuffer__C_idupdates(1))
  done

lemma setMR_getMR:
  "setMR s i (getMR s i) = s"
  apply (simp add:setMR_def getMR_def ipc_buffer_ptr_def ipc_buffer_def)
  apply (subst msg_update_id)
  apply simp
  done

lemma setMR_setMR[simp]:"setMR (setMR s i x) i y = setMR s i y"
  apply (simp add:setMR_def ipc_buffer_ptr_def ipc_buffer_def fun_upd_def)
  apply (subst comp_def, subst update_update)
  apply simp
  done

lemma setMR_reorder:"setMR (setMR s i x) j y = (if i = j then setMR s j y else setMR (setMR s j y) i x)"
  apply simp
  apply (simp add:setMR_def ipc_buffer_ptr_def ipc_buffer_def fun_upd_def comp_def)
  done

lemma setMR_preserves_inv[simp]:"inv s \<Longrightarrow> inv (setMR s i x)"
  apply (clarsimp simp:inv_defs setMR_def)
  done

lemma tls_mr_distinct[simp]:"tls (setMR s x y) = tls s"
  apply (clarsimp simp:tls_def tls_ptr_def setMR_def ipc_buffer_ptr_def ipc_buffer_def)
  done

/*- endif -*/
