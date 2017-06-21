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

/*- if 'autocorres/packed.thy' not in included -*/
/*- do included.add('autocorres/packed.thy') -*/

/*- include 'autocorres/getmr_setmr.thy' -*/

definition
  packed :: "lifted_globals \<Rightarrow> word32 list \<Rightarrow> bool"
where
  "packed s xs =
    (length xs \<le> unat seL4_MsgMaxLength \<and> list_all (\<lambda>(i, v). getMR s i = v) (enumerate 0 xs))"

lemma packed_empty[simp]: "packed s []"
  by (simp add:packed_def)

lemma packed_eq:"\<lbrakk>packed s xs; packed s ys; length xs = length ys\<rbrakk> \<Longrightarrow> xs = ys"
  apply (rule nth_equalityI)
   apply assumption
  unfolding packed_def apply clarsimp
  apply (drule_tac i=i in list_all_nth, simp)+
  apply (simp add:split_beta fst_enumerate snd_enumerate)
  done

lemma packed_length:"packed s xs \<Longrightarrow> length xs \<le> unat seL4_MsgMaxLength"
  by (simp add:packed_def)

lemma packed_setmr[simp]:"packed (setMR s 0 x) [x]"
  apply (clarsimp simp:packed_def getMR_setMR seL4_MsgMaxLength_def)
  done

lemma getmr_packed:"\<lbrakk>packed s xs; i < length xs\<rbrakk> \<Longrightarrow> getMR s i = xs ! i"
  apply (clarsimp simp:packed_def)
  apply (subst (asm) list_all_iff)
  apply (erule_tac x="(i, xs ! i)" in ballE)
   apply clarsimp
  apply (subgoal_tac "(i, xs ! i) \<in> set (enumerate 0 xs)")
   apply simp
  apply (rule enumerate_member[where n=0, simplified])
  apply simp
  done

lemma packed_extend:"\<And>x. \<lbrakk>i < unat seL4_MsgMaxLength; i = length xs; packed s xs\<rbrakk> \<Longrightarrow> packed (setMR s i x) (xs @ [x])"
  apply (clarsimp simp:packed_def)
  apply (subst enumerate_append)
  apply (subst list_all_append)
  apply clarsimp
  apply (cut_tac s=s and i="length xs" and j="length xs" and v=x in getMR_setMR)
   apply (clarsimp simp:seL4_MsgMaxLength_def)+
  apply (cut_tac xs="enumerate 0 xs" and ys = "enumerate 0 xs" and
                 f="\<lambda>(i, y). getMR (setMR s (length xs) x) i = y" and
                 g="\<lambda>(i, y). getMR s i = y" in list_all_cong)
    apply (clarsimp simp:seL4_MsgMaxLength_def)+
   apply (subst getMR_setMR)
    apply (subgoal_tac "a < length xs")
     apply (clarsimp simp:seL4_MsgMaxLength_def)
    apply (rule_tac b=b in enumerate_bound[where n=0, simplified])
    apply assumption
   apply (clarsimp simp:enumerate_exceed[where n=0, simplified])
  apply clarsimp
  done

lemma packed_equiv:"\<And>x. \<lbrakk>i < unat seL4_MsgMaxLength; i = length xs\<rbrakk> \<Longrightarrow> packed s xs = packed (setMR s i x) (xs @ [x])"
  apply (rule iffI)
   apply (rule packed_extend, clarsimp+)
  apply (clarsimp simp:packed_def)
  apply (subst (asm) enumerate_append)
  apply (subst (asm) list_all_append)
  apply clarsimp
  apply (cut_tac xs="enumerate 0 xs" and ys="enumerate 0 xs" and f="\<lambda>(i, v). getMR s i = v" and
                 g="\<lambda>(i, y). getMR (setMR s (length xs) x) i = y" in list_all_cong)
    apply clarsimp+
   apply (drule_tac b=b in enumerate_bound[where n=0, simplified])
   apply (subst getMR_setMR)
    apply (clarsimp simp:seL4_MsgMaxLength_def)+
  done

/*- endif -*/
