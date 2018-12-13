/*#
 *# Copyright 2018, Data61
 *# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 *# ABN 41 687 119 230.
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(DATA61_BSD)
 #*/

(* /*? macros.generated_file_notice() ?*/ *)

/*? macros.check_isabelle_outfile(
        '%s_CDL_Refine' % options.verification_base_name, outfile_name) ?*/
/*- set cdl_thy = '%s_CDL' % options.verification_base_name -*/
/*- set arch_spec_thy = '%s_Arch_Spec' % options.verification_base_name -*/

theory "/*? options.verification_base_name ?*/_CDL_Refine"
imports
  /*? arch_spec_thy ?*/ (* generated arch spec *)
  /*? cdl_thy ?*/ (* generated CDL spec *)
  "CamkesCdlRefine.Policy_CAMKES_CDL"
  "DPolicy.Dpolicy"
  "Lib.FastMap"
begin

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
\<close>

ML \<open>
(* The FastMap package expects the input in sorted order,
   we need to sort the object IDs by numeric value. *)
fun /*? options.verification_base_name ?*/_id_value ctxt obj_name =
    Proof_Context.get_thm ctxt ("/*? cdl_thy ?*/." ^ obj_name ^ "_id_def")
    |> Thm.prop_of
    |> Logic.dest_equals |> snd
    |> HOLogic.dest_number |> snd;

val /*? options.verification_base_name ?*/_obj_labels =
  sort (apply2 (fst #> /*? options.verification_base_name ?*/_id_value @{context}) #> int_ord)
    /*- for not_first, (obj, label) in enumerate(sorted(object_label_mapping(), key=lambda('x: x[0].name'))) -*/
      /*? ',' if not_first else '[' ?*/ ("/*? obj.name ?*/", "/*? label ?*/")
    /*- endfor -*/
    ];
\<close>

local_setup \<open>
  let
    val mapping = /*? options.verification_base_name ?*/_obj_labels
       |> map (fn (obj, label) => (Const ("/*? cdl_thy ?*/." ^ obj ^ "_id", @{typ cdl_object_id}),
                                   HOLogic.mk_string label));
    val key_getter = @{term "id :: word32 \<Rightarrow> word32"};
    val extra_simps = @{thms /*? cdl_thy ?*/.ids};
  in
    FastMap.define_map
      (FastMap.name_opts_default "/*? options.verification_base_name ?*/_labelling")
      mapping
      key_getter
      extra_simps
      false
  end
\<close>
print_theorems

definition /*? options.verification_base_name ?*/_admissible_labelling :: "label agent_map \<Rightarrow> bool"
  where
  "/*? options.verification_base_name ?*/_admissible_labelling label_of \<equiv>
      (\<forall>i l. /*? options.verification_base_name ?*/_labelling i = Some l \<longrightarrow> label_of i = l)"

lemma /*? options.verification_base_name ?*/_admissible_labelling_default:
  "/*? options.verification_base_name ?*/_admissible_labelling (the o /*? options.verification_base_name ?*/_labelling)"
  by (simp add: /*? options.verification_base_name ?*/_admissible_labelling_def)

text \<open>Make sure that an admissible labelling exists.\<close>
corollary /*? options.verification_base_name ?*/_admissible_labelling_exists:
  "\<exists>label_of. /*? options.verification_base_name ?*/_admissible_labelling label_of"
  by (blast intro: /*? options.verification_base_name ?*/_admissible_labelling_default)

text \<open>
  Helper to unfold the list of object-to-label mappings.
  The conclusion of admissible_labelling_values will be a conjunction of
  equations for the label_of function.
\<close>
lemma iterate_labelling_helper:
  "\<lbrakk> /*? options.verification_base_name ?*/_admissible_labelling label_of;
     /*? options.verification_base_name ?*/_labelling = map_of binds;
     distinct (map fst binds)
   \<rbrakk> \<Longrightarrow> list_all (\<lambda>(k, v). label_of k = v) binds"
  unfolding /*? options.verification_base_name ?*/_admissible_labelling_def
  by (blast intro: list_allI FastMap.map_of_lookups)

lemmas admissible_labelling_values =
  iterate_labelling_helper[
    OF _ /*? options.verification_base_name ?*/_labelling_to_lookup_list /*? options.verification_base_name ?*/_labelling_keys_distinct,
    simplified FastMap.list_all_dest prod.case]

subsection \<open>Sanity checks for object labelling\<close>

text \<open>
  Check that we always label certain important objects with the obvious
  component name. We check this for each component's:

  \begin{itemize}
    \item Control TCB
    \item Root CNode (CAmkES only generates one CNode level for each component,
          so this suffices for now)
    \item PD and its PTs
    \item TCB root caps (this also covers the CNode and PD, but includes
          additional things like the IPC buffer frame)
  \end{itemize}
\<close>
lemma /*? options.verification_base_name ?*/_admissible_labelling__tcbs_correct:
  "/*? options.verification_base_name ?*/_admissible_labelling label_of \<Longrightarrow>
      (
/*- for not_first, c in enumerate(me.composition.instances) -*/
      /*? '\\<and>' if not_first else ' ' ?*/ label_of /*? c.name ?*/_cnode_id = ''/*? c.name ?*/''
      \<and> label_of /*? '%s_%d' % (c.name, len(c.name)) ?*/_0_control_9_tcb_id = ''/*? c.name ?*/''
      \<and> label_of /*? c.name ?*/_group_bin_pd_id = ''/*? c.name ?*/''
      \<and> (\<forall>cap \<in> ran /*? '%s_%d' % (c.name, len(c.name)) ?*/_0_control_9_tcb_caps. \<forall>i \<in> cap_objects cap. label_of i = ''/*? c.name ?*/'')
      \<and> (\<forall>pt_i \<in> mapped_pts_of /*? cdl_thy ?*/.objects /*? c.name ?*/_group_bin_pd_caps. label_of pt_i = ''/*? c.name ?*/'')
/*- endfor -*/
      )"
  apply (drule admissible_labelling_values)
  apply (clarsimp simp: mapped_pts_of_def object_slots_def
                        /*? cdl_thy ?*/.cap_defs /*? cdl_thy ?*/.obj_defs /*? cdl_thy ?*/.objects)
  done

text \<open>
  Also check that all labels are inhabited.
\<close>
lemma /*? options.verification_base_name ?*/_admissible_labelling__all_labels_inhabited:
  "/*? options.verification_base_name ?*/_admissible_labelling label_of \<Longrightarrow>
/*- for not_first, c in enumerate(me.composition.instances + me.composition.connections) -*/
     /*? '\\<and>' if not_first else ' ' ?*/ (\<exists>obj. label_of obj = ''/*? c.name ?*/'')
/*- endfor -*/
  "
  apply (drule admissible_labelling_values)
  apply (elim conjE)
  apply (intro conjI; erule exI)
  done

(* FIXME: more sanity checks *)


section \<open>More helpers\<close>

definition /*? options.verification_base_name ?*/_policy
  where
  "/*? options.verification_base_name ?*/_policy \<equiv> policy_of /*? arch_spec_thy ?*/.assembly'"


schematic_goal /*? options.verification_base_name ?*/_component_names:
  "components (composition /*? arch_spec_thy ?*/.assembly') = ?comps"
  apply (clarsimp simp: /*? arch_spec_thy ?*/.assembly'_def
                        /*? arch_spec_thy ?*/.composition'_def)
  apply (rule refl)
  done

schematic_goal /*? options.verification_base_name ?*/_connections:
  "connections (composition /*? arch_spec_thy ?*/.assembly') = ?spec"
  apply (clarsimp simp: /*? arch_spec_thy ?*/.assembly'_def
                        /*? arch_spec_thy ?*/.composition'_def
/*- for c in me.composition.instances + me.composition.connections -*/
                        /*? arch_spec_thy ?*/./*? c.name ?*/_def
/*- endfor -*/
        )
  apply (rule refl)
  done

text \<open>
  Resolve a schematic equality of the form
  "((a1 = x1 \<and> a2 = x2 \<and> \<dots>) \<or> (b1 = y1 \<and> b2 = y2 \<and> \<dots>) \<or> \<dots>) = ?val",
  while ensuring that the LHS consists of equations in disjunctive normal form.
\<close>
method assign_schematic_dnf =
  ((rule disj_cong, assign_schematic_eq_conjs)+, assign_schematic_eq_conjs)

lemma split_Collect_graph_edge:
  "Collect P = Collect (\<lambda>(from, auth, to). P (from, auth, to))"
  by simp

lemma Collect_graph_cong_helper:
  "(\<And>x y z. P x y z = P' x y z) \<Longrightarrow>
   Collect (\<lambda>(x, y, z). P x y z) = Collect (\<lambda>(x, y, z). P' x y z)"
  by simp

schematic_goal /*? options.verification_base_name ?*/_policy_def':
  "/*? options.verification_base_name ?*/_policy = ?PAS"
  apply (clarsimp simp:
            policy_of_def connector_simps
            /*? options.verification_base_name ?*/_policy_def /*? options.verification_base_name ?*/_component_names /*? options.verification_base_name ?*/_connections
            Collect_Int_pred_eq Collect_union)
  apply (subst split_Collect_graph_edge)
  apply (rule Collect_graph_cong_helper)
  apply (clarsimp simp: Groebner_Basis.dnf cong: conj_cong rev_conj_cong)
  apply assign_schematic_dnf
  done

(*
 * From /*? options.verification_base_name ?*/_policy_def', generate a list of rules of the form
 *   "(''subj'', auth, ''obj'') \<in> /*? options.verification_base_name ?*/_policy"
 *)
schematic_goal /*? options.verification_base_name ?*/_policy_gen_cases_:
  "((subj, auth, obj) \<in> /*? options.verification_base_name ?*/_policy) = ?cases"
  apply (clarsimp simp only: /*? options.verification_base_name ?*/_policy_def' mem_Collect_eq)
  by assign_schematic_dnf

lemma subst_eqn_helper:
  "(\<And>s. s = t \<longrightarrow> P s) \<Longrightarrow> P t"
  by simp

local_setup {* fn ctxt => let
    fun try_repeat f x = case try f x of SOME x' => try_repeat f x' | NONE => x;
    (* convert "(a = x \<and> b = y \<and> \<dots>) \<longrightarrow> foo a b \<dots>" to "foo x y \<dots>" *)
    val subst_values =
          REPEAT_ALL_NEW (resolve_tac @{context} @{thms conjI}) 1
          #> Seq.hd
          #> Simplifier.rewrite_rule @{context} @{thms atomize_imp}
          #> try_repeat (fn t => t RS @{thm subst_eqn_helper});
    fun process thm =
          case try subst_values thm of
              SOME eqn => [eqn]
            | NONE => process (@{thm disjI1} RS thm) @ process (@{thm disjI2} RS thm);
    val /*? options.verification_base_name ?*/_policy_intros = process @{thm /*? options.verification_base_name ?*/_policy_gen_cases_[THEN iffD2]};
  in
    ctxt
    |> Local_Theory.notes [((Binding.name "/*? options.verification_base_name ?*/_policy_intros", []),
                            [(/*? options.verification_base_name ?*/_policy_intros, [])])]
    |> snd
  end
*}
thm /*? options.verification_base_name ?*/_policy_intros

section \<open>Admissible PAS\<close>

text \<open>
  This defines a set of policies that fit our arch spec and cap layout.
\<close>
definition /*? options.verification_base_name ?*/_admissible_pas :: "label PAS \<Rightarrow> bool"
  where
  "/*? options.verification_base_name ?*/_admissible_pas pas \<equiv>
     /*? options.verification_base_name ?*/_admissible_labelling (pasObjectAbs pas) \<and>
     pasSubject pas \<in> fst ` set (components (composition /*? arch_spec_thy ?*/.assembly')) \<and>
     /*? options.verification_base_name ?*/_policy \<subseteq> pasPolicy pas"

text \<open>Again, ensure that admissible policies exist.\<close>
lemma /*? options.verification_base_name ?*/_admissible_pas_exists:
  "\<exists>pas. /*? options.verification_base_name ?*/_admissible_pas pas"
  apply (insert /*? options.verification_base_name ?*/_admissible_labelling_exists)
  apply (erule exE, rename_tac poa)
  (* For now, just fill in the fields we need. *)
  apply (rule_tac x = "undefined\<lparr>
                         pasObjectAbs := poa,
                         pasPolicy := /*? options.verification_base_name ?*/_policy,
                         pasSubject := fst (hd (components (composition /*? arch_spec_thy ?*/.assembly')))
                         \<rparr>"
                  in exI)

  apply (simp add: /*? options.verification_base_name ?*/_admissible_pas_def /*? options.verification_base_name ?*/_connections /*? options.verification_base_name ?*/_component_names)
  done

text \<open>
  Simplified, automation-friendl(ier) intro for policy_wellformed, assuming that
  CAmkES never provides Grant auth across components and IRQs are disabled.
\<close>

lemma camkes_policy_wellformedI:
  assumes "\<not>maySendIrqs"
      and "\<And>a. (agent, a, agent) \<in> aag"
      and "\<And>s auth r. (s, auth, r) \<in> aag \<Longrightarrow> (s, Control, s) \<in> aag"
      and "\<And>s r. (s, Grant, r) \<in> aag \<Longrightarrow> s = r"
      and "\<And>s r. (s, Control, r) \<in> aag \<Longrightarrow> s = r"
      and "\<And>s auth. (s, Control, s) \<in> aag \<Longrightarrow> (s, auth, s) \<in> aag"
      and "\<And>s r. (s, Receive, r) \<in> aag \<Longrightarrow> s \<noteq> r \<Longrightarrow> (r, Control, r) \<in> aag \<Longrightarrow> False"
      and "\<And>s r. (s, Call, r) \<in> aag \<Longrightarrow> s \<noteq> r \<Longrightarrow> (r, Control, r) \<in> aag \<Longrightarrow> False"
      and "\<And>s ep. (s, Call, ep) \<in> aag \<Longrightarrow> (s, SyncSend, ep) \<in> aag"
      and "\<And>s r. (s, Reply, r) \<in> aag \<Longrightarrow> (r, DeleteDerived, s) \<in> aag"
      and "\<And>s r ep. (s, Call, ep) \<in> aag \<Longrightarrow> s \<noteq> ep \<Longrightarrow> (r, Receive, ep) \<in> aag
                     \<Longrightarrow> (r, Reply, s) \<in> aag"
      and "\<And>l1 l2 l3. (l1, DeleteDerived, l2) \<in> aag \<Longrightarrow> l1 \<noteq> l2 \<Longrightarrow> (l2, DeleteDerived, l3) \<in> aag
                       \<Longrightarrow> (l1, DeleteDerived, l3) \<in> aag"
  shows "policy_wellformed aag maySendIrqs irqSet agent"
  unfolding policy_wellformed_def
  apply (insert assms)
  apply (safe; metis)
  done

text \<open>
  Checking the transitivity conditions for @{const policy_wellformed} is quadratic in
  the size of our policy; here we extract relevant subsets of the policy cases to
  make things a bit faster.

  Ultimately, we would like to prove a generic @{const policy_wellformed} theorem for
  all @{const policy_of} outputs, but the current messiness of
  @{const policy_of} and @{const wellformed_assembly} are not conducive for that.
\<close>

lemmas /*? options.verification_base_name ?*/_policy_cases_Control =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "Control", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_Receive =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "Receive", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_Reply =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "Reply", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_Grant =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "Grant", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_Call =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "Call", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_DeleteDerived =
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "DeleteDerived", simplified]
lemmas /*? options.verification_base_name ?*/_policy_cases_DeleteDerived2 =
/*- for c in me.composition.instances -*/
  /*? options.verification_base_name ?*/_policy_cases_DeleteDerived[where subj = "''/*? c.name ?*/''", simplified]
/*- endfor -*/

text \<open>
  Ensure that our base access policy is wellformed.
  This lets us extend it to other wellformed policies.
\<close>
lemma /*? options.verification_base_name ?*/_policy_wellformed:
  "\<lbrakk> pasPolicy aag = /*? options.verification_base_name ?*/_policy;
     pasSubject aag \<in> fst ` set (components (composition /*? arch_spec_thy ?*/.assembly'));
     \<not> pasMaySendIrqs aag \<comment> \<open>ignore IRQs for now\<close>
   \<rbrakk> \<Longrightarrow> pas_wellformed aag"
  apply clarsimp
  apply (rule camkes_policy_wellformedI)
             (* IRQs disabled *)
             apply blast
            (* Components are agents *)
            apply (fastforce simp: /*? options.verification_base_name ?*/_connections /*? options.verification_base_name ?*/_component_names
                            intro: /*? options.verification_base_name ?*/_policy_intros)
           (* All subjects have self Control *)
           apply (drule /*? options.verification_base_name ?*/_policy_gen_cases_[THEN iffD1])
           apply (fast intro: /*? options.verification_base_name ?*/_policy_intros)
          (* Grant confinement *)
          apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Grant[THEN iffD1]
                          intro: /*? options.verification_base_name ?*/_policy_intros)
         (* Control confinement *)
         apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                         intro: /*? options.verification_base_name ?*/_policy_intros)
        (* Control implies all rights *)
        apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                        intro: /*? options.verification_base_name ?*/_policy_intros)
       (* Components are not Receive targets *)
       apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Receive[THEN iffD1]
                              /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                       intro: /*? options.verification_base_name ?*/_policy_intros)
      (* Components are not Call targets *)
      apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                             /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                      intro: /*? options.verification_base_name ?*/_policy_intros)
     (* Call implies SyncSend *)
     apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                     intro: /*? options.verification_base_name ?*/_policy_intros)
    (* Reply implies DeleteDerived *)
    apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Reply[THEN iffD1]
                    intro: /*? options.verification_base_name ?*/_policy_intros)
   (* Call + Receive implies Reply *)
   apply (fast dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                     /*? options.verification_base_name ?*/_policy_cases_Receive[THEN iffD1]
              intro: /*? options.verification_base_name ?*/_policy_intros)
  (* DeleteDerived is transitive *)
  apply (drule /*? options.verification_base_name ?*/_policy_cases_DeleteDerived[THEN iffD1];
         elim conjE disjE;
         (simp only: simp_thms cong: disj_cong)?;
         drule /*? options.verification_base_name ?*/_policy_cases_DeleteDerived2[THEN iffD1];
         (simp only: simp_thms cong: disj_cong)?;
         elim conjE disjE;
         simp only: /*? options.verification_base_name ?*/_policy_intros)
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

lemma iterate_add_map_helper:
  (* m0 will be empty_irq_objects *)
  "\<lbrakk> (m0 ++ m(k \<mapsto> v)) a = Some b;
     \<lbrakk> a = k; b = v \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> (m0 ++ m) a = Some b \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  (* \<open>simp split: if_split\<close> loops *)
  apply simp
  apply (subst (asm) if_split[where P="\<lambda>x. x = _"])
  apply fastforce
  done

lemma iterate_map_helper:
  "\<lbrakk> (m(k \<mapsto> v)) a = Some b;
     \<lbrakk> a = k; b = v \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> m a = Some b \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  using iterate_add_map_helper[where m0=Map.empty]
  by fastforce

lemma case_obj_helper:
  "\<lbrakk> (case (m0 ++ m(k \<mapsto> v)) a of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap;
     \<lbrakk> a = k; s v b = Some cap \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> (case (m0 ++ m) a of None \<Rightarrow> n | Some y \<Rightarrow> s y) b = Some cap \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (simp split: if_splits)

lemmas object_slots_eval_simps =
    object_slots_def cdl_object.case
    cdl_asid_pool.simps
    cdl_cnode.simps
    cdl_irq_node.simps
    cdl_page_table.simps
    cdl_page_directory.simps
    cdl_tcb.simps



section \<open>CAmkES-capDL refinement proof\<close>

text \<open>Helpers to put the policy subgoals into a consistent form for our automation\<close>
lemma helper_pcs_refined_policyI:
  assumes cdt_policy: "\<And>p slot p' slot'.
                          cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                          (pasObjectAbs aag p', Control, pasObjectAbs aag p) \<in> pasPolicy aag"
      and delete_derived_policy: "\<And>p slot p' slot'.
                          cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                          (pasObjectAbs aag p', DeleteDerived, pasObjectAbs aag p) \<in> pasPolicy aag"
      and obj_policy: "\<And>p p_obj p_idx cap auth oref.
                          \<lbrakk> cdl_objects s p = Some p_obj;
                            object_slots p_obj p_idx = Some cap;
                            auth \<in> cdl_cap_auth_conferred cap;
                            oref \<in> cdl_obj_refs cap
                          \<rbrakk> \<Longrightarrow> (pasObjectAbs aag p, auth, pasObjectAbs aag oref) \<in> pasPolicy aag"
  shows "auth_graph_map (pasObjectAbs aag) (cdl_state_objs_to_policy s) \<subseteq> (pasPolicy aag)"
  apply (clarsimp simp: cdl_state_objs_to_policy_def auth_graph_map_def)
  by (fastforce elim: cdl_state_bits_to_policy.cases
                intro: obj_policy cdt_policy delete_derived_policy
                simp: opt_cap_def slots_of_def opt_object_def
                split: option.splits)

text \<open>FIXME: Our capDL assigns no ASIDs, so there's not much to do here right now.\<close>
lemma /*? options.verification_base_name ?*/_asid_policy_trivial:
  "cdl_state_asids_to_policy pas /*? cdl_thy ?*/.state \<subseteq> pasPolicy pas"
  apply (clarsimp simp: /*? cdl_thy ?*/.state_def /*? cdl_thy ?*/.asid_table_def
                        opt_cap_def slots_of_def opt_object_def object_slots_def)
  apply (erule cdl_state_asids_to_policy_aux.cases)
    (* ASIDs in CDL heap*)
    (* unfold object map *)
    apply clarsimp
    apply (simp only: /*? cdl_thy ?*/.objects_def)

    (* traverse mapping *)
    apply (match premises in
                "case_option _ _ ((_ ++ _(_ \<mapsto> obj)) _) _ = _" for obj \<Rightarrow> \<open>print_term obj\<close>,
           erule case_obj_helper,
           time_methods \<open>solves \<open>simp add: /*? cdl_thy ?*/.obj_defs;
                                 (simp only: /*? cdl_thy ?*/.cap_defs,
                                  (erule iterate_map_helper, solves \<open>simp\<close>)+,
                                  solves \<open>simp\<close>)\<close>\<close>)+
    apply (solves \<open>clarsimp simp: /*? cdl_thy ?*/.empty_irq_objects_def /*? cdl_thy ?*/.empty_irq_node_def
                            split: if_split_asm\<close>)
   (* ASID lookup case *)
   apply blast
  (* ASID pool case *)
  apply blast
  done

text \<open>FIXME: Our capDL assigns no IRQs, so there's not much to do here right now.\<close>
lemma /*? options.verification_base_name ?*/_irq_policy_trivial:
  "cdl_state_irqs_to_policy pas /*? cdl_thy ?*/.state \<subseteq> pasPolicy pas"
  apply clarsimp
  apply (erule cdl_state_irqs_to_policy_aux.cases)
  apply (clarsimp simp: /*? cdl_thy ?*/.state_def /*? cdl_thy ?*/.irqs_def
                        opt_cap_def slots_of_def opt_object_def object_slots_def)
  (* unfold object map *)
  apply (simp only: /*? cdl_thy ?*/.objects_def)

  (* traverse mapping *)
  apply (match premises in
              "case_option _ _ ((_ ++ _(_ \<mapsto> obj)) _) _ = _" for obj \<Rightarrow> \<open>print_term obj\<close>,
         erule case_obj_helper,
         time_methods \<open>solves \<open>simp add: /*? cdl_thy ?*/.obj_defs;
                               (simp only: /*? cdl_thy ?*/.cap_defs,
                                (erule iterate_map_helper, solves \<open>simp\<close>)+,
                                solves \<open>simp\<close>)\<close>\<close>)+
  apply (solves \<open>clarsimp simp: /*? cdl_thy ?*/.empty_irq_objects_def /*? cdl_thy ?*/.empty_irq_node_def
                          split: if_split_asm\<close>)
  done

text \<open>Main integrity proof\<close>

theorem /*? options.verification_base_name ?*/_pcs_refined:
  assumes other_assms:
     "pas_wellformed pas"
     (* TODO *) "cdl_irq_map_wellformed pas /*? cdl_thy ?*/.state"
     (* TODO *) "cdl_tcb_domain_map_wellformed pas /*? cdl_thy ?*/.state"
  assumes admissible_pas:
     "/*? options.verification_base_name ?*/_admissible_pas pas"
  shows
     "pcs_refined pas /*? cdl_thy ?*/.state"
proof -
  from admissible_pas have /*? options.verification_base_name ?*/_policy:
    "/*? options.verification_base_name ?*/_policy \<subseteq> pasPolicy pas"
    by (simp add: /*? options.verification_base_name ?*/_admissible_pas_def)

  (* HACK to split the labelling values theorem into multiple equations.
     We put them into the simpset for fast lookup during the proof procedure.
     This uses the conjuncts attribute from Lib, which stashes the result into
     the dynamic theorem "conjuncts". We retrieve it from there. *)
  note dummy = admissible_labelling_values
            [OF /*? options.verification_base_name ?*/_admissible_pas_def[simplified atomize_eq, THEN iffD1, THEN conjunct1],
             OF admissible_pas, simplified atomize_conj[symmetric], conjuncts]
  note labelling_values = conjuncts
  (* end hack *)

  show ?thesis
    apply (clarsimp simp only: simp_thms
                               pcs_refined_def other_assms
                               /*? options.verification_base_name ?*/_asid_policy_trivial /*? options.verification_base_name ?*/_irq_policy_trivial
                    del: subsetI)
    apply (rule helper_pcs_refined_policyI)
      text \<open>
         CDT properties.
         FIXME: Our capDL assigns an empty CDT, so there's not much to do here right now.
      \<close>
      apply ((fastforce simp: /*? cdl_thy ?*/.state_def /*? cdl_thy ?*/.cdt_def)+)[2]

    text \<open>Object case.\<close>
    apply (clarsimp simp: /*? cdl_thy ?*/.state_def)

    (* Assume /*? options.verification_base_name ?*/_policy is concrete enough and we don't need any
       default policy rules from pas_wellformed. *)
    apply (rule subsetD[OF /*? options.verification_base_name ?*/_policy])

    (* Unfold big object mapping. *)
    apply (simp only: /*? cdl_thy ?*/.objects_def)

    (* Cache rulesets to speed up the "solve policy" steps slightly *)
    supply /*? options.verification_base_name ?*/_policy_intros[intro!]
    supply labelling_values[simp]

    (* Iterate through all objects and their contained caps (if any) *)
    apply (match premises in
                "(_ ++ _(_ \<mapsto> obj)) _ = _" for obj \<Rightarrow> \<open>print_term obj\<close>,
           (* trivial case: objects without caps *)
           time_methods
             cap_non_container_tac:
                 \<open>erule iterate_add_map_helper,
                  solves \<open>simp only: object_slots_def /*? cdl_thy ?*/.obj_defs
                                     option.inject option.distinct cdl_object.case\<close>\<close>
           (* nontrivial case: objects with caps *)
          |time_methods
             cap_to_container_tac:
                 \<open>erule iterate_add_map_helper,
                  (* Substitute object value and then remove it (to reduce clutter) *)
                  simp only:,
                  thin_tac "p_obj = _",
                  solves \<open>(simp add: /*? cdl_thy ?*/.cap_defs /*? cdl_thy ?*/.obj_defs,
                           (* Evaluate object_slots, but do not unfold cap maps
                              inside the objects yet *)
                           simp only: object_slots_eval_simps);
                          (time_methods "  contained cap auth":
                              \<open>match premises in
                                 "(_(_ \<mapsto> child_cap)) _ = _"
                                    for child_cap \<Rightarrow> \<open>print_term child_cap\<close>,
                               erule iterate_map_helper,
                               time_methods "    solve policy":
                                 \<open>fastforce simp: cdl_cap_auth_conferred_def
                                                  cap_rights_to_auth_def
                                                  vspace_cap_rights_to_auth_def\<close>\<close>)+,
                           solves \<open>simp only: option.distinct\<close>\<close>\<close>)+

    (* Assert that we have processed all normal objects *)
    apply (match premises in "(empty_irq_objects ++ Map.empty) _ = Some _" \<Rightarrow> succeed)

    text \<open>FIXME: Our capDL assigns no IRQs, so there's not much to do here right now.\<close>
    apply (clarsimp simp: /*? cdl_thy ?*/.empty_irq_objects_def /*? cdl_thy ?*/.empty_irq_node_def
                          object_slots_def
                    split: if_split_asm)
    done
qed

end
