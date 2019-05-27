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
  "CamkesCdlRefine.Eval_CAMKES_CDL"
  "DPolicy.Dpolicy"
  "Lib.FastMap"
  "Lib.RangeMap"
  "Lib.FP_Eval"
  "Lib.TermPatternAntiquote"
begin

section \<open>System-specific policy definitions\<close>
text \<open>
  We need to label objects in a way that matches the architecture spec
  and also allows the cap layout to satisfy the access policy.
\<close>

section \<open>Expand policy rules\<close>

definition /*? options.verification_base_name ?*/_policy
  where
  "/*? options.verification_base_name ?*/_policy \<equiv> policy_of /*? arch_spec_thy ?*/.assembly'"

/*# FIXME: naming scheme duplicated from arch-definitions #*/
/*- if hasattr(me, 'name') and me.name is not none -*/
    /*- set assembly_name = me.name -*/
/*- else -*/
    /*- set assembly_name = 'assembly\'' -*/
/*- endif -*/
/*- if hasattr(me.composition, 'name') and me.composition.name is not none -*/
    /*- set composition_name = me.composition.name -*/
/*- else -*/
    /*- set composition_name = 'composition\'' -*/
/*- endif -*/

schematic_goal /*? options.verification_base_name ?*/_component_names:
  "components (composition /*? arch_spec_thy ?*/.assembly') = ?comps"
  apply (clarsimp simp: /*? arch_spec_thy ?*/./*? assembly_name ?*/_def
                        /*? arch_spec_thy ?*/./*? composition_name ?*/_def)
  apply (rule refl)
  done

schematic_goal /*? options.verification_base_name ?*/_connections:
  "connections (composition /*? arch_spec_thy ?*/.assembly') = ?spec"
  apply (clarsimp simp: /*? arch_spec_thy ?*/./*? assembly_name ?*/_def
                        /*? arch_spec_thy ?*/./*? composition_name ?*/_def
/*- for c in me.composition.instances -*/
                        /*? arch_spec_thy ?*/./*? isabelle_component(c.name) ?*/_def
/*- endfor -*/
/*- for c in me.composition.connections -*/
                        /*? arch_spec_thy ?*/./*? isabelle_connection(c.name) ?*/_def
/*- endfor -*/
        )
  apply (rule refl)
  done

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

local_setup \<open>fn ctxt => let
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
    val /*? options.verification_base_name ?*/_policy_intros =
          process @{thm /*? options.verification_base_name ?*/_policy_gen_cases_[THEN iffD2]}
          |> distinct Thm.eq_thm_prop; (* remove dups *)
  in
    ctxt
    |> Local_Theory.notes [((Binding.name "/*? options.verification_base_name ?*/_policy_intros", []),
                            [(/*? options.verification_base_name ?*/_policy_intros, [])])]
    |> snd
  end
\<close>
thm /*? options.verification_base_name ?*/_policy_intros


section \<open>Object label mappings\<close>

text \<open>
  Construct mapping of integrity labels for each object.
\<close>

ML \<open>
(* The RangeMap package expects the input in sorted order,
   we need to sort the object IDs by numeric value. *)
fun /*? options.verification_base_name ?*/_id_value ctxt obj_name =
    Proof_Context.get_thm ctxt ("/*? cdl_thy ?*/." ^ obj_name ^ "_id_def")
    |> Thm.prop_of
    |> Logic.dest_equals |> snd
    |> HOLogic.dest_number |> snd;

val /*? options.verification_base_name ?*/_obj_labels =
      (* object name, size bits, policy label *)
    /*- set delim = namespace(value='[') -*//*# need this nonsense to modify variable -- see jinja2 docs #*/
    /*- for (obj, label) in sorted(object_label_mapping(), key=lambda('x: x[0].name')) -*/
      /*- if not obj.name.startswith('root_untyped_') -*//*# Exclude root untypeds because they overlap other objects and have no policy. FIXME: better way to detect these #*/
        /*? delim.value ?*/ ("/*? isabelle_capdl_ident(obj.name) ?*/", /*? obj.get_size_bits() ?*/, "/*? label ?*/")
        /*- set delim.value = ',' -*/
      /*- endif -*/
    /*- endfor -*/
    ]
    |> sort (apply2 (#1 #> /*? options.verification_base_name ?*/_id_value @{context}) #> int_ord);

val id_value : string -> int =
  fn id =>
    Proof_Context.get_thm @{context} (id ^ "_def")
    |> Thm.rhs_of |> Thm.term_of |> HOLogic.dest_number |> snd;

(* Now construct our mapping from (ptr, ptr + 2^sz) to labels *)
val /*? options.verification_base_name ?*/_label_entries =
  /*? options.verification_base_name ?*/_obj_labels
  |> map (fn (obj_name, sz, label) => ("/*? cdl_thy ?*/." ^ obj_name ^ "_id", sz, label))
  |> map (fn (id, sz, label) =>
            ((Const (id, @{typ cdl_object_id}),
              @{term "(+) :: cdl_object_id \<Rightarrow> _ \<Rightarrow> _"} $
                Const (id, @{typ cdl_object_id}) $
                (@{term "(^) 2 :: _ \<Rightarrow> cdl_object_id"} $ HOLogic.mk_number @{typ nat} sz)),
             HOLogic.mk_string label))
  |> map (fn (range, label) =>
      (apply2 (Thm.cterm_of @{context}) range, Thm.cterm_of @{context} label));
\<close>

local_setup \<open>
  RangeMap.define_map (RangeMap.name_opts_default "/*? options.verification_base_name ?*/_label")
      /*? options.verification_base_name ?*/_label_entries @{typ cdl_object_id} @{typ label}
      (FP_Eval.eval_conv @{context}
        (FP_Eval.make_rules @{thms word_rel_simps_small word_pow_arith_simps /*? cdl_thy ?*/.ids} []))
\<close>
(* we will primarily use these *)
lemmas /*? options.verification_base_name ?*/_label_lookups =
  /*? options.verification_base_name ?*/_label.start_lookups
    [unfolded /*? options.verification_base_name ?*/_label.tree_list_lookup_eq]

text \<open>
  Define admissible labelling functions to be those that are consistent
  with the mapping we defined above.
\<close>

definition /*? options.verification_base_name ?*/_labelling :: "cdl_object_id \<Rightarrow> string option"
  where
  "/*? options.verification_base_name ?*/_labelling x \<equiv> map_option snd (RangeMap.range_map_of /*? options.verification_base_name ?*/_label.list x)"

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
      /*? '\\<and>' if not_first else ' ' ?*/ label_of /*? isabelle_capdl_identifier(c.name) ?*/_cnode_id = ''/*? c.name ?*/''
      \<and> label_of /*? isabelle_capdl_identifier('%s_%s_0_control_tcb_id' % (c.name, c.name.replace('.', '_'))) ?*/ = ''/*? c.name ?*/''/*#
  XXX: the extra 'replace' in the second name component duplicates what the camkes tool does internally #*/
      \<and> label_of /*? isabelle_capdl_identifier('%s_group_bin_pd_id' % c.name) ?*/ = ''/*? c.name ?*/''
      \<and> (\<forall>cap \<in> ran /*? isabelle_capdl_identifier('%s_%s_0_control_tcb_caps' % (c.name, c.name.replace('.', '_'))) ?*/. \<forall>i \<in> cap_objects cap. label_of i = ''/*? c.name ?*/'')/*# XXX: ditto here #*/
      \<and> (\<forall>pt_i \<in> mapped_pts_of /*? cdl_thy ?*/.objects /*? isabelle_capdl_identifier('%s_group_bin_pd_caps' % c.name) ?*/. label_of pt_i = ''/*? c.name ?*/'')
/*- endfor -*/
      )"
  (* FIXME: cleanup *)
  apply (simp only: rel_simps arith_simps simp_thms if_False if_True conj_assoc imp_disjL
                    option.map prod.sel
                    ball_simps bex_simps fun_upd_apply ran_map_upd ran_empty
                    finite_set_simps
                    cdl_cap.case cap_objects.simps mapped_pts_of_def object_slots_def

                    /*? options.verification_base_name ?*/_CDL.cap_defs
                    /*? options.verification_base_name ?*/_CDL.obj_defs
                    /*? options.verification_base_name ?*/_CDL.objects_lookups

                    /*? options.verification_base_name ?*/_admissible_labelling_def
                    /*? options.verification_base_name ?*/_labelling_def
                    /*? options.verification_base_name ?*/_label_lookups
              cong: imp_cong)
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
  apply (simp add: /*? options.verification_base_name ?*/_admissible_labelling_def
                   /*? options.verification_base_name ?*/_labelling_def)
  apply (fastforce intro: /*? options.verification_base_name ?*/_label_lookups)
  done

(* FIXME: more sanity checks *)


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
  /*? options.verification_base_name ?*/_policy_gen_cases_[where auth = "auth.Grant", simplified]
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
             (* Components may not send IRQs *)
             subgoal
               apply blast
               done
            (* Components are agents *)
            subgoal
              apply (fastforce simp: /*? options.verification_base_name ?*/_connections /*? options.verification_base_name ?*/_component_names
                               intro: /*? options.verification_base_name ?*/_policy_intros)
              done
           (* All subjects have self Control *)
           subgoal
             apply (drule /*? options.verification_base_name ?*/_policy_gen_cases_[THEN iffD1])
             apply (fast intro: /*? options.verification_base_name ?*/_policy_intros)
             done
          (* Grant confinement *)
          subgoal
            apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Grant[THEN iffD1]
                             intro: /*? options.verification_base_name ?*/_policy_intros)
            done
         (* Control confinement *)
         subgoal
           apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                            intro: /*? options.verification_base_name ?*/_policy_intros)
           done
        (* Control implies all rights *)
        subgoal
          apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                           intro: /*? options.verification_base_name ?*/_policy_intros)
          done
       (* Components are not Receive targets *)
       subgoal
         apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Receive[THEN iffD1]
                                /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                         intro: /*? options.verification_base_name ?*/_policy_intros)
         done
      (* Components are not Call targets *)
      subgoal
        apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                               /*? options.verification_base_name ?*/_policy_cases_Control[THEN iffD1]
                         intro: /*? options.verification_base_name ?*/_policy_intros)
        done
     (* Call implies SyncSend *)
     subgoal
       apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                        intro: /*? options.verification_base_name ?*/_policy_intros)
       done
    (* Reply implies DeleteDerived *)
    subgoal
      apply (fastforce dest: /*? options.verification_base_name ?*/_policy_cases_Reply[THEN iffD1]
                       intro: /*? options.verification_base_name ?*/_policy_intros)
      done
   (* Call + Receive implies Reply *)
   subgoal
     apply (fast dest: /*? options.verification_base_name ?*/_policy_cases_Call[THEN iffD1]
                       /*? options.verification_base_name ?*/_policy_cases_Receive[THEN iffD1]
                 intro: /*? options.verification_base_name ?*/_policy_intros)
     done
  (* DeleteDerived is transitive (see also VER-1030) *)
  subgoal
    apply (drule /*? options.verification_base_name ?*/_policy_cases_DeleteDerived[THEN iffD1];
           elim conjE disjE;
           (simp only: simp_thms cong: disj_cong)?;
           drule /*? options.verification_base_name ?*/_policy_cases_DeleteDerived2[THEN iffD1];
           (simp only: simp_thms cong: disj_cong)?;
           elim conjE disjE;
           (simp only:)?;
           (rule /*? options.verification_base_name ?*/_policy_intros)?)
    done
  done



section \<open>CAmkES-capDL refinement proof\<close>

(* specialise ptr_range rewrite rule *)
lemmas /*? options.verification_base_name ?*/_label_over_ptr_range =
  label_over_ptr_range[
      (* FP_Eval only supports first-order matching, so instantiate P *)
      where P = "\<lambda>l. (_, _, l) \<in> _" and label_spec = /*? options.verification_base_name ?*/_labelling,
      OF /*? options.verification_base_name ?*/_label.list_monotonic,
      (* expand labelling into tree lookup *)
      unfolded /*? options.verification_base_name ?*/_labelling_def, OF refl]
lemmas /*? options.verification_base_name ?*/_label_over_ptr_range_cases =
  /*? options.verification_base_name ?*/_label_lookups[THEN /*? options.verification_base_name ?*/_label_over_ptr_range]

text \<open>FIXME: Our capDL assigns no ASIDs, so there's not much to do here right now.\<close>
lemma /*? options.verification_base_name ?*/_asid_policy_trivial:
  assumes admissible_pas:
     "/*? options.verification_base_name ?*/_admissible_pas pas"
  shows
    "cdl_state_asids_to_policy pas /*? options.verification_base_name ?*/_CDL.state \<subseteq> pasPolicy pas"
proof -
  (* everything needed to evaluate asid integrity... *)
  note obj_policy_eval_simps' =
        /*? options.verification_base_name ?*/_label_lookups
        /*? options.verification_base_name ?*/_CDL.obj_defs
        (* Map.empty is actually an abbrev for a lambda, which fp_eval
           doesn't allow as a rule LHS. Rewrite eagerly first *)
        (* FIXME: generate these with map_of in the first place.
           Also fix "rev ..." in graph_of_map_of__sorted_eval *)
        /*? options.verification_base_name ?*/_CDL.cap_defs[simplified fun_upds_to_map_of]
        /*? options.verification_base_name ?*/_label_over_ptr_range_cases

        obj_policy_eval_simps

  show ?thesis
    apply (rule cdl_state_asids_to_policy__eval[where
                  policy_spec=/*? options.verification_base_name ?*/_policy and
                  obj_label_spec=/*? options.verification_base_name ?*/_labelling and
                  asid_label_spec="\<lambda>_. None"
           ])
        using admissible_pas /*? options.verification_base_name ?*/_admissible_pas_def apply blast
       using admissible_pas /*? options.verification_base_name ?*/_admissible_pas_def /*? options.verification_base_name ?*/_admissible_labelling_def apply blast
      apply blast

     (* ASIDs in objects *)
     apply (simp only: /*? options.verification_base_name ?*/_labelling_def)
     apply (tactic \<open>let
              val rules = @{thms /*? options.verification_base_name ?*/_CDL.state_def cdl_state.simps
                                 /*? options.verification_base_name ?*/_CDL.objects_to_lookup_list
                                 graph_of_map_of__distinct_eval if_True
                                 /*? options.verification_base_name ?*/_CDL.objects_keys_distinct};
              val congs = @{thms obj_policy_eval_congs};
              in SUBGOAL (fn _ => FP_Eval.eval_tac @{context} (FP_Eval.make_rules rules congs) 1)
                         1 end\<close>)
     (* this is a separate step for now, because graph_of_map_of__sorted_eval
        won't work for objects list *)
     apply (tactic \<open>let
              val rules = @{thms obj_policy_eval_simps'};
              val congs = @{thms obj_policy_eval_congs};
              val conv = rpair FP_Eval.skel0
                       #> FP_Eval.eval @{context} (FP_Eval.make_rules rules congs)
                       #> tap (fn (_, c) => tracing ("fp_eval counters: " ^ @{make_string} c))
                       #> fst #> fst;
              in SUBGOAL (fn _ => Conv.gconv_rule conv 1 #> Seq.succeed) 1 end\<close>;
            intro TrueI conjI /*? options.verification_base_name ?*/_policy_intros)

    (* ASID pools *)
    apply (simp add: /*? options.verification_base_name ?*/_CDL.state_def /*? options.verification_base_name ?*/_CDL.asid_table_def graph_of_def)
    done
qed

text \<open>FIXME: Our capDL assigns no IRQs, so there's not much to do here right now.\<close>
lemma /*? options.verification_base_name ?*/_irq_policy_trivial:
  assumes admissible_pas:
     "/*? options.verification_base_name ?*/_admissible_pas pas"
  shows
    "cdl_state_irqs_to_policy pas /*? options.verification_base_name ?*/_CDL.state \<subseteq> pasPolicy pas"
proof -
  (* everything needed to evaluate asid integrity... *)
  note obj_policy_eval_simps' =
        /*? options.verification_base_name ?*/_label_lookups
        /*? options.verification_base_name ?*/_CDL.obj_defs
        (* Map.empty is actually an abbrev for a lambda, which fp_eval
           doesn't allow as a rule LHS. Rewrite eagerly first *)
        (* FIXME: generate these with map_of in the first place.
           Also fix "rev ..." in graph_of_map_of__sorted_eval *)
        /*? options.verification_base_name ?*/_CDL.cap_defs[simplified fun_upds_to_map_of]
        /*? options.verification_base_name ?*/_label_over_ptr_range_cases

        obj_policy_eval_simps

  show ?thesis
    apply (rule cdl_state_irqs_to_policy__eval[where
                  policy_spec=/*? options.verification_base_name ?*/_policy and
                  obj_label_spec=/*? options.verification_base_name ?*/_labelling and
                  irq_label_spec="\<lambda>_. None"
           ])
       using admissible_pas /*? options.verification_base_name ?*/_admissible_pas_def apply blast
      using admissible_pas /*? options.verification_base_name ?*/_admissible_pas_def /*? options.verification_base_name ?*/_admissible_labelling_def apply blast
     apply blast

    apply (simp only: /*? options.verification_base_name ?*/_labelling_def)
    apply (tactic \<open>let
             val rules = @{thms /*? options.verification_base_name ?*/_CDL.state_def cdl_state.simps
                                /*? options.verification_base_name ?*/_CDL.objects_to_lookup_list
                                graph_of_map_of__distinct_eval if_True
                                /*? options.verification_base_name ?*/_CDL.objects_keys_distinct};
             val congs = @{thms obj_policy_eval_congs};
             in SUBGOAL (fn _ => FP_Eval.eval_tac @{context} (FP_Eval.make_rules rules congs) 1)
                        1 end\<close>)
    (* this is a separate step for now, because graph_of_map_of__sorted_eval
       won't work for objects list *)
    apply (tactic \<open>let
             val rules = @{thms obj_policy_eval_simps'};
             val congs = @{thms obj_policy_eval_congs};
             val conv = rpair FP_Eval.skel0
                      #> FP_Eval.eval @{context} (FP_Eval.make_rules rules congs)
                      #> tap (fn (_, c) => tracing ("fp_eval counters: " ^ @{make_string} c))
                      #> fst #> fst;
             in SUBGOAL (fn _ => Conv.gconv_rule conv 1 #> Seq.succeed) 1 end\<close>;
           intro TrueI conjI /*? options.verification_base_name ?*/_policy_intros)
    done
qed

text \<open>Main integrity proof\<close>

theorem /*? options.verification_base_name ?*/_pcs_refined:
  assumes other_assms:
     "pas_wellformed pas"
     (* TODO *) "cdl_irq_map_wellformed pas /*? options.verification_base_name ?*/_CDL.state"
     (* TODO *) "cdl_tcb_domain_map_wellformed pas /*? options.verification_base_name ?*/_CDL.state"
  assumes admissible_pas:
     "/*? options.verification_base_name ?*/_admissible_pas pas"
  shows
     "pcs_refined pas /*? options.verification_base_name ?*/_CDL.state"
proof -
  from admissible_pas have /*? options.verification_base_name ?*/_policy:
    "/*? options.verification_base_name ?*/_policy \<subseteq> pasPolicy pas"
    by (simp add: /*? options.verification_base_name ?*/_admissible_pas_def)

  (* everything needed to evaluate object integrity... *)
  note obj_policy_eval_simps' =
        /*? options.verification_base_name ?*/_label_lookups
        /*? options.verification_base_name ?*/_CDL.obj_defs
        (* Map.empty is actually an abbrev for a lambda, which fp_eval
           doesn't allow as a rule LHS. Rewrite eagerly first *)
        (* FIXME: generate these with map_of in the first place.
           Also fix "rev ..." in graph_of_map_of__sorted_eval *)
        /*? options.verification_base_name ?*/_CDL.cap_defs[simplified fun_upds_to_map_of]
        /*? options.verification_base_name ?*/_label_over_ptr_range_cases

        obj_policy_eval_simps

  show ?thesis
    apply (clarsimp simp only: simp_thms
                               pcs_refined_def other_assms
                               /*? options.verification_base_name ?*/_asid_policy_trivial[OF admissible_pas]
                               /*? options.verification_base_name ?*/_irq_policy_trivial[OF admissible_pas]
                    del: subsetI)
    apply (rule helper_pcs_refined_policy__eval[
                  where policy_spec = /*? options.verification_base_name ?*/_policy
                    and label_spec = /*? options.verification_base_name ?*/_labelling])
        (* instantiate policy specs *)
        apply (rule /*? options.verification_base_name ?*/_policy)
       using admissible_pas /*? options.verification_base_name ?*/_admissible_pas_def /*? options.verification_base_name ?*/_admissible_labelling_def
       apply blast

      text \<open>
         CDT properties.
         FIXME: Our capDL assigns an empty CDT, so there's not much to do here right now.
      \<close>
      apply ((fastforce simp: /*? options.verification_base_name ?*/_CDL.state_def /*? options.verification_base_name ?*/_CDL.cdt_def)+)[2]

    text \<open>Object case.\<close>
    apply (simp only: /*? options.verification_base_name ?*/_labelling_def)
    (* this is a separate step for now, because graph_of_map_of__sorted_eval
       won't work for objects list *)
    apply (tactic \<open>let
             val rules = @{thms /*? options.verification_base_name ?*/_CDL.state_def cdl_state.simps
                                /*? options.verification_base_name ?*/_CDL.objects_to_lookup_list
                                graph_of_map_of__distinct_eval if_True
                                /*? options.verification_base_name ?*/_CDL.objects_keys_distinct};
             val congs = @{thms obj_policy_eval_congs};
             in SUBGOAL (fn _ => FP_Eval.eval_tac @{context} (FP_Eval.make_rules rules congs) 1)
                        1 end\<close>)
    (* this is a separate step for now, because graph_of_map_of__sorted_eval
       won't work for objects list *)
    apply (tactic \<open>let
             val rules = @{thms obj_policy_eval_simps'};
             val congs = @{thms obj_policy_eval_congs};
             val conv = rpair FP_Eval.skel0
                      #> FP_Eval.eval @{context} (FP_Eval.make_rules rules congs)
                      #> tap (fn (_, c) => tracing ("fp_eval counters: " ^ @{make_string} c))
                      #> fst #> fst;
             in SUBGOAL (fn _ => Conv.gconv_rule conv 1 #> Seq.succeed) 1 end\<close>;
           intro TrueI conjI /*? options.verification_base_name ?*/_policy_intros)
    done
qed

end
