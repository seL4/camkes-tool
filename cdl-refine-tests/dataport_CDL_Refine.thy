(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory dataport_CDL_Refine
imports
  dataport_Arch_Spec (* generated arch spec *)
  dataport_CDL (* generated CDL spec *)
  "CamkesCdlRefine.Policy_CAMKES_CDL"
  "DPolicy.Dpolicy"
begin

(* This file is *not* generated. Yet. *)

abbreviation "arch_spec \<equiv> dataport_Arch_Spec.assembly'"
abbreviation "cdl_state \<equiv> dataport_CDL.state"

text \<open>Helper lemma sets. FIXME: Most of these should be moved.\<close>
lemmas word_eq_simps =
    simp_thms arith_simps rel_simps
    bintrunc_numeral_simps bintrunc_numeral_simps(5)[folded numeral_One]
    bintr_num BIT_bin_simps BIT_special_simps
    len_of_numeral_defs numeral_One[symmetric] pred_numeral_simps
    word_eq_numeral_iff_iszero not_iszero_numeral iszero_word_no

(* test *)
lemma "P (0x123 \<noteq> (0x234 :: cdl_object_id)) = P True"
  apply (simp only: word_eq_simps)
  done

(* Prove that cap IDs are unequal without unfolding their values *)
simproc_setup dataport_CDL_id_equality ("(x :: cdl_object_id) = y") = \<open>
  fn _ => fn ctxt => fn ct =>
    case Thm.term_of ct of
        Const (@{const_name HOL.eq}, _) $ Const (id1, _) $ Const (id2, _) =>
            if String.isPrefix "dataport_CDL." id1 andalso String.isSuffix "_id" id1
               andalso String.isPrefix "dataport_CDL." id2 andalso String.isSuffix "_id" id2
            then SOME (Simplifier.rewrite (ctxt addsimps @{thms dataport_CDL.ids}) ct)
            else NONE
      | _ => NONE
\<close>



section \<open>Generic policy labelling helpers\<close>
(* FIXME: MOVE *)
text \<open>Retrieve all frames and page tables mapped into a page directory.\<close>
definition mapped_pts_of :: "cdl_heap \<Rightarrow> cdl_cap_map \<Rightarrow> cdl_object_id set"
  where
  "mapped_pts_of object_map pd_caps \<equiv>
      {pt_id. \<exists>pt \<in> ran pd_caps. pt_id \<in> cap_objects pt}"

definition mapped_frames_of :: "cdl_heap \<Rightarrow> cdl_cap_map \<Rightarrow> cdl_object_id set"
  where
  "mapped_frames_of object_map pd_caps \<equiv>
      {frame_id.
         \<exists>pt_id \<in> mapped_pts_of object_map pd_caps.
           \<exists>frame \<in> ran (object_slots (the (object_map pt_id))).
             frame_id \<in> cap_objects frame}"

text \<open>
  Resolve a schematic equality "{a, b, c, ...} = ?val", while checking
  that the LHS is a concrete set builder expression
\<close>
method assign_schematic_set =
  ((rule arg_cong[where f="insert _"])+, rule refl[where t="{}"])

text \<open>
  Resolve a schematic equality "(a = x \<and> b = y \<and> c = z \<and> \<dots>) = ?val",
  while checking that the LHS is a conjunction of equations
\<close>
method assign_schematic_eq_conjs =
  ((rule conj_cong[where P="_ = _", OF refl])+, rule refl[where t="_ = _"])



section \<open>System-specific policy definitions\<close>
text \<open>
  We need to label objects in a way that matches the architecture spec
  and also allows the cap layout to satisfy the access policy.

  We assert that each component's threads, CNodes, VSpaces, private frames,
  etc. are labelled with that component's name. We also assert that shared
  objects used for connectors are labelled with the connectors' names.
\<close>

(* FIXME: we're not sure which frame was generated for which dataport *)
definition simple1_shared_objs :: "cdl_object_id set"
  where
  "simple1_shared_objs \<equiv> {
      frame_comp2_group_bin_0012_id
   }"

definition simple2_shared_objs :: "cdl_object_id set"
  where
  "simple2_shared_objs \<equiv> {
      frame_comp2_group_bin_0014_id
   }"

definition comp1_comp2_shared_objs :: "cdl_object_id set"
  where
  "comp1_comp2_shared_objs \<equiv>
      simple1_shared_objs
    \<union> simple2_shared_objs"

definition this_admissible_labelling :: "label agent_map \<Rightarrow> bool"
  where
  "this_admissible_labelling label_of \<equiv>
      ( label_of comp2_cnode_id = ''comp2''
      \<and> label_of comp2_5_0_control_9_tcb_id = ''comp2''
      \<and> (\<forall>cap \<in> ran comp2_cnode_caps. \<forall>i \<in> cap_objects cap.
              i \<notin> comp1_comp2_shared_objs \<longrightarrow> label_of i = ''comp2'')
      \<and> (\<forall>cap \<in> ran comp2_5_0_control_9_tcb_caps. \<forall>i \<in> cap_objects cap. label_of i = ''comp2'')
      \<and> (\<forall>pt_i \<in> mapped_pts_of objects comp2_group_bin_pd_caps. label_of pt_i = ''comp2'')
      \<and> (\<forall>frame_i \<in> mapped_frames_of objects comp2_group_bin_pd_caps.
             frame_i \<notin> comp1_comp2_shared_objs \<longrightarrow> label_of frame_i = ''comp2'')

      \<and> label_of comp1_cnode_id = ''comp1''
      \<and> label_of comp1_5_0_control_9_tcb_id = ''comp1''
      \<and> (\<forall>cap \<in> ran comp1_cnode_caps. \<forall>i \<in> cap_objects cap.
              i \<notin> comp1_comp2_shared_objs \<longrightarrow> label_of i = ''comp1'')
      \<and> (\<forall>cap \<in> ran comp1_5_0_control_9_tcb_caps. \<forall>i \<in> cap_objects cap. label_of i = ''comp1'')
      \<and> (\<forall>pt_i \<in> mapped_pts_of objects comp1_group_bin_pd_caps. label_of pt_i = ''comp1'')
      \<and> (\<forall>frame_i \<in> mapped_frames_of objects comp1_group_bin_pd_caps.
             frame_i \<notin> comp1_comp2_shared_objs \<longrightarrow> label_of frame_i = ''comp1'')

      \<and> (\<forall>i \<in> simple1_shared_objs. label_of i = ''simple1'')

      \<and> (\<forall>i \<in> simple2_shared_objs. label_of i = ''simple2'')
      )"

subsection \<open>Evaluate cap sets\<close>

schematic_goal comp1_mapped_pts:
  "mapped_pts_of objects comp1_group_bin_pd_caps = ?val"
  apply (clarsimp simp: mapped_pts_of_def cap_defs obj_defs objects object_slots_def)
  apply (clarsimp simp only: Collect_disj_eq singleton_conv)
  apply clarsimp
  apply assign_schematic_set
  done

schematic_goal comp1_mapped_frames:
  "mapped_frames_of objects comp1_group_bin_pd_caps = ?val"
  apply (clarsimp simp: mapped_frames_of_def comp1_mapped_pts)
  apply (clarsimp simp: cap_defs obj_defs objects object_slots_def)
  apply (clarsimp simp only: Collect_disj_eq singleton_conv)
  apply clarsimp
  apply assign_schematic_set
  done

schematic_goal comp2_mapped_pts:
  "mapped_pts_of objects comp2_group_bin_pd_caps = ?val"
  apply (clarsimp simp: mapped_pts_of_def cap_defs obj_defs objects object_slots_def)
  apply (clarsimp simp only: Collect_disj_eq singleton_conv)
  apply clarsimp
  apply assign_schematic_set
  done

schematic_goal comp2_mapped_frames:
  "mapped_frames_of objects comp2_group_bin_pd_caps = ?val"
  apply (clarsimp simp: mapped_frames_of_def comp2_mapped_pts)
  apply (clarsimp simp: cap_defs obj_defs objects object_slots_def)
  apply (clarsimp simp only: Collect_disj_eq singleton_conv)
  apply clarsimp
  apply assign_schematic_set
  done

subsection \<open>Expand @{const this_admissible_labelling} to get a list of label equations\<close>
schematic_goal this_admissible_def':
  "this_admissible_labelling l = ?def"
  (* TODO: optimise *)
  apply (clarsimp simp: this_admissible_labelling_def)
  apply (clarsimp simp: comp1_mapped_pts comp1_mapped_frames
                        comp2_mapped_pts comp2_mapped_frames)
  apply (clarsimp simp: cap_defs objects obj_defs object_slots_def
                        comp1_comp2_shared_objs_def
                        simple1_shared_objs_def simple2_shared_objs_def)
  apply assign_schematic_eq_conjs
  done

subsection \<open>Make sure that an admissible labelling exists.\<close>

lemma exists_labelling_new_val:
  "\<lbrakk> \<And>f. P f \<Longrightarrow> P (f(k := v)); \<exists>f. P f \<rbrakk> \<Longrightarrow> \<exists>f. f k = v \<and> P f"
  apply (erule exE, rename_tac f)
  apply (rule_tac x="f(k := v)" in exI)
  apply simp
  done

lemma exists_labelling_new_vals:
  "\<lbrakk> \<And>f. P f \<Longrightarrow> P (f(k := v)); \<exists>f. P f \<rbrakk> \<Longrightarrow> \<exists>f. (f k = v \<or> ignore f) \<and> P f"
  apply (metis exists_labelling_new_val)
  done

lemma this_admissible_labelling_exists:
  "\<exists>label_of. this_admissible_labelling label_of"
  apply (unfold this_admissible_def')

  (* iterate over each equation set *)
  apply (time_methods "handle clause":
           \<open>rule exists_labelling_new_val exists_labelling_new_vals,
            (* FIXME: use ID simproc instead of ids *)
            (simp (no_asm_use) only: fun_upd_same fun_upd_other word_eq_simps ids;
             elim conjE; blast
            )\<close>)+
  (* base case, single equation set *)
  apply fastforce
  done

(* FIXME: more sanity checks *)


section \<open>More helpers\<close>

lemma split_Collect_graph_edge:
  "Collect P = Collect (\<lambda>(from, auth, to). P (from, auth, to))"
  by simp

definition this_policy
  where
  "this_policy \<equiv> policy_of dataport_Arch_Spec.assembly'"


schematic_goal arch_spec_def:
  "arch_spec = ?spec"
  apply (clarsimp simp: assembly'_def composition'_def
           simple1_def simple2_def Buf_def
           comp1_def comp2_def DataportTest_def)
  apply (rule refl)
  done

text \<open>
  Resolve a schematic equality of the form
  "((a1 = x1 \<and> a2 = x2 \<and> \<dots>) \<or> (b1 = y1 \<and> b2 = y2 \<and> \<dots>) \<or> \<dots>) = ?val",
  while ensuring that the LHS consists of equations in disjunctive normal form.
\<close>
method assign_schematic_dnf =
  ((rule disj_cong, assign_schematic_eq_conjs)+, assign_schematic_eq_conjs)

lemma Collect_3ple_cong_helper:
  "(\<And>x y z. P x y z = P' x y z) \<Longrightarrow>
   Collect (\<lambda>(x, y, z). P x y z) = Collect (\<lambda>(x, y, z). P' x y z)"
  by simp

schematic_goal this_policy_def':
  "this_policy = ?PAS"
  apply (clarsimp simp:
            policy_of_def connector_simps
            this_policy_def arch_spec_def
            Collect_Int_pred_eq Collect_union)
  apply (subst split_Collect_graph_edge)
  apply (clarsimp simp: Groebner_Basis.dnf cong: conj_cong rev_conj_cong)
  apply (rule Collect_3ple_cong_helper)
  apply assign_schematic_dnf
  done


section \<open>Admissible PAS\<close>

text \<open>
  This defines a set of policies that fit our arch spec and cap layout.
\<close>
definition this_admissible_pas :: "label PAS \<Rightarrow> bool"
  where
  "this_admissible_pas pas \<equiv>
     this_admissible_labelling (pasObjectAbs pas) \<and>
     pasSubject pas \<in> fst ` set (components (composition dataport_Arch_Spec.assembly')) \<and>
     this_policy \<subseteq> pasPolicy pas"

text \<open>Again, ensure that admissible policies exist.\<close>
lemma this_admissible_pas_exists:
  "\<exists>pas. this_admissible_pas pas"
  apply (insert this_admissible_labelling_exists)
  apply (erule exE, rename_tac poa)
  (* For now, just fill in the fields we need. *)
  apply (rule_tac x = "undefined\<lparr>
                         pasObjectAbs := poa,
                         pasPolicy := this_policy,
                         pasSubject := fst (hd (components (composition dataport_Arch_Spec.assembly')))
                         \<rparr>"
                  in exI)

  apply (simp add: this_admissible_pas_def arch_spec_def)
  done

text \<open>
  Ensure that our base access policy is wellformed.
  This lets us extend it to other wellformed policies.
\<close>
lemma this_policy_wellformed:
  "\<lbrakk> pasPolicy aag = this_policy;
     pasSubject aag \<in> fst ` set (components (composition arch_spec));
     \<not> pasMaySendIrqs aag (* ignore IRQs for now *)
   \<rbrakk> \<Longrightarrow> pas_wellformed aag"
  apply (clarsimp simp: policy_wellformed_def policy_of_def
                        this_policy_def' arch_spec_def)
  apply_trace (safe; simp)
  done



section \<open>More helpers\<close>

(* FIXME: Gap in the Dpolicy model, object ID semantic mismatch between ASpec and DSpec (VER-924) *)
lemma cdl_obj_refs_frame_cheat:
  "cdl_obj_refs (cdl_cap.FrameCap dev x rs sz is_real asid) = {x}"
  sorry
declare cdl_obj_refs.simps(16)[simp del]
declare cdl_obj_refs_frame_cheat[simp]

lemmas cdl_obj_refs_cheat_simps =
  cdl_obj_refs.simps(1-15) cdl_obj_refs_frame_cheat cdl_obj_refs.simps(17-)

lemma case_obj_helper':
  "\<lbrakk> (case (if c then Some y else m) of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap;
     \<lbrakk> c; s y b = Some cap \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> \<not>c; (case m of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto split: if_splits)

(* this version forgets the \<not>c's, to avoid them piling up *)
lemma case_obj_helper:
  "\<lbrakk> (case (if c then Some y else m) of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap;
     \<lbrakk> c; s y b = Some cap \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> (case m of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (rule case_obj_helper')

(* FIXME: maybe merge with case_obj_helper *)
lemma cap_container_helper:
  "\<lbrakk> (if c then a else b) = x;
     \<lbrakk> c; a = x \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> b = x \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (simp split: if_splits)

text \<open>For unfolding cap container iterations in @{const this_admissible_pas}\<close>
lemma cap_map_ran_helper:
  "\<lbrakk> \<forall>cap\<in>ran (m(i \<mapsto> c)). P cap; i \<notin> dom m; \<lbrakk> P c; \<forall>cap\<in>ran m. P cap \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (clarsimp simp: ran_def split: if_splits)
  apply metis
  done

lemma in_map_dom:
  "(x \<in> dom (m(k \<mapsto> v))) = (x = k \<or> x \<in> dom m)"
  "x \<notin> dom Map.empty"
  by auto



section \<open>CAmkES-capDL refinement proof\<close>

text \<open>Our capDL assigns no ASIDs, so we trivially satisfy the ASID policy\<close>
lemma this_asid_policy_trivial:
  "cdl_state_asids_to_policy pas cdl_state \<subseteq> pasPolicy pas"
  apply (clarsimp simp: dataport_CDL.state_def dataport_CDL.asid_table_def
                        opt_cap_def slots_of_def opt_object_def object_slots_def)
  apply (erule cdl_state_asids_to_policy_aux.cases)
    (* ASIDs in CDL heap*)
    (* unfold object map *)
    apply (clarsimp simp: dataport_CDL.objects_def)

    (* traverse mapping *)
    apply (erule case_obj_helper,
           time_methods \<open>solves \<open>clarsimp simp: dataport_CDL.obj_defs dataport_CDL.cap_defs
                                          split: if_split_asm\<close>\<close>)+
    apply (solves \<open>clarsimp simp: dataport_CDL.empty_irq_objects_def dataport_CDL.empty_irq_node_def
                            split: if_split_asm\<close>)
   (* ASID lookup case *)
   apply blast
  (* ASID pool case *)
  apply blast
  done

text \<open>Our capDL assigns no IRQs, so we trivially satisfy the IRQ policy\<close>
lemma this_irq_policy_trivial:
  "cdl_state_irqs_to_policy pas cdl_state \<subseteq> pasPolicy pas"
  apply clarsimp
  apply (erule cdl_state_irqs_to_policy_aux.cases)
  apply (clarsimp simp: dataport_CDL.state_def dataport_CDL.irqs_def
                        opt_cap_def slots_of_def opt_object_def object_slots_def)
  (* unfold object map *)
  apply (clarsimp simp: dataport_CDL.objects_def)

  (* traverse mapping *)
  apply (erule case_obj_helper,
         time_methods \<open>solves \<open>clarsimp simp: dataport_CDL.obj_defs dataport_CDL.cap_defs
                                        split: if_split_asm\<close>\<close>)+
  apply (solves \<open>clarsimp simp: dataport_CDL.empty_irq_objects_def dataport_CDL.empty_irq_node_def
                          split: if_split_asm\<close>)
  done

text \<open>Main integrity proof\<close>
theorem this_pcs_refined:
  assumes other_assms:
     "pas_wellformed pas"
     "cdl_irq_map_wellformed pas cdl_state"
     "cdl_tcb_domain_map_wellformed pas cdl_state"
  shows
  "this_admissible_pas pas \<Longrightarrow> pcs_refined pas cdl_state"
  apply (clarsimp simp: pcs_refined_def other_assms this_asid_policy_trivial this_irq_policy_trivial)

  (* Now the main proof for the pasPolicy graph *)
  apply (clarsimp simp:
            cdl_state_objs_to_policy_def auth_graph_map_def)
  apply (erule cdl_state_bits_to_policy.cases)

  (* CDT case is trivial:  CDT is empty *)
  prefer 2
   apply (fastforce simp: dataport_CDL.state_def dataport_CDL.cdt_def)

  (* Cap map case *)
  apply (clarsimp simp:
            opt_cap_def slots_of_def opt_object_def
            this_admissible_pas_def
            arch_spec_def
            dataport_CDL.state_def)

  apply (unfold this_admissible_def', elim conjE)

  (* assume this_policy is concrete enough and we don't need any
     default policy rules from pas_wellformed *)
  apply (erule subsetD)

  (* unfold big object mapping *)
  apply (clarsimp simp: dataport_CDL.objects_def)

  (* iterate mapping *)
  apply (time_methods
           cap_non_container_tac:
               \<open>erule case_obj_helper,
                solves \<open>simp (no_asm_use) add: object_slots_def dataport_CDL.obj_defs\<close>\<close>
        |time_methods
           cap_to_container_tac:
               \<open>erule case_obj_helper,
                solves \<open>clarsimp simp: object_slots_def dataport_CDL.cap_defs dataport_CDL.obj_defs;
                        (time_methods "  contained cap auth":
                            \<open>erule cap_container_helper,
                             (clarsimp simp only:
                                  cdl_cap_auth_conferred_def
                                  cap_rights_to_auth_def vspace_cap_rights_to_auth_def
                                  cdl_cap.case cdl_obj_refs_cheat_simps
                                  this_policy_def';
                              simp (no_asm_use);
                              blast)\<close>)+,
                         solves \<open>simp only: option.distinct\<close>\<close>\<close>)+

  (* IRQ case is trivial: we have no IRQs *)
  apply (clarsimp simp: dataport_CDL.empty_irq_objects_def dataport_CDL.empty_irq_node_def
                        object_slots_def)
  apply (simp (no_asm_use) split: if_split_asm)
  done

end
