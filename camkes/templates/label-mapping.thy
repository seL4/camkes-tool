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

/*- set thy = CapDLLabels -*/
theory "/*? thy ?*/" imports
  CapDLSpec (* generated *)
  "~~/../l4v/camkes/cdl-refine/Generator_CAMKES_CDL"
  ArchSpec (* generated *)
  "~~/../l4v/lib/LemmaBucket"
  "~~/../l4v/lib/WordLemmaBucket"
  "~~/../l4v/proof/access-control/Access"
begin

/*# Ignore the comment below. It is intended to apply to the generated output,
 *# not this template.
 #*/
(* THIS THEORY IS GENERATED. DO NOT EDIT.
 * It is expected to be hosted in l4v/camkes/cdl-refine.
 *)

/*# Forced garbage collection that we emit between proofs when debugging in
 *# order to keep an interactive Isabelle session manageable.
 #*/
/*- set gc = 'ML {* PolyML.fullGC () *}' if options.verbosity >= 2 else '' -*/

/*# Helpers for emitting different proof styles depending on whether debugging
 *# is enabled. This is useful for (a) speeding up completed proofs and (b)
 *# streamlining proof development. We construct the proofs in this file as
 *# monolithic `by` invocations. This is horrible style, but in a large system
 *# the thousands of `apply` commands take a long time to process and hold up
 *# work on further proofs that depend on their results.
 #*/
/*- set open_proof = 'sorry (*\n  apply (' if options.verbosity >= 2 else 'by (' -*/ /*# XXX: fix syntax highlighting: *) #*/
/*- set a = 'apply (' if options.verbosity >= 2 else '    ' -*/
/*- set A = ')' if options.verbosity >= 2 else ',' -*/
/*- set close_proof = ')\n  done *)' if options.verbosity >= 2 else ')' -*/

/*- macro solve_with(step) -*/((/*? step ?*/); fail)/*- endmacro -*/

/*# Tags for IDs that map to nothing and fake IRQ CNodes, respectively. These
 *# are simply chosen such that they won't conflict with any existing component
 *# instance or connection names.
 #*/
/*- set garbage_tag = ' garbage' -*/
/*- set irq_tag = ' irq' -*/

definition
  tags :: "tag set"
where
  "tags \<equiv> {/*? ', '.join(map(lambda('x: \'\\\'\\\'%s\\\'\\\'\' % x'), obj_space.labels)) ?*/} \<union> {''/*? garbage_tag ?*/'', ''/*? irq_tag ?*/''}"

/*- macro emit_map(name, data, domain_type, range_type, as_if=False) -*/
  /*? assert(isinstance(name, six.string_types)) ?*/
  /*? assert(isinstance(data, dict)) ?*/
  /*? assert(isinstance(domain_type, six.string_types)) ?*/
  /*? assert(isinstance(range_type, six.string_types)) ?*/
  /*? assert(isinstance(as_if, bool)) ?*/
(** TPP: condense = True *)
definition /*? name ?*/ :: "/*? domain_type ?*/ \<Rightarrow> /*? range_type ?*/ option"
  /*- if as_if -*/
  where "/*? name ?*/ \<equiv> (\<lambda>ident.
    /*- for k, v in data.items() -*/
    if ident = /*? k ?*/ then Some /*? v ?*/ else
    /*- endfor -*/
    None)"
  /*- else -*/
  where "/*? name ?*/ \<equiv> [
    /*- for k, v in data.items() -*/
    /*? k ?*/ \<mapsto> /*? v ?*//*- if not loop.last -*/,/*- endif -*/
    /*- endfor -*/
    ]"
  /*- endif -*/
(** TPP: condense = False *)

/*- if False -*/
(** TPP: condense = True *)
lemma /*? name ?*/_domain: "dom /*? name ?*/ = {/*? ', '.join(data.keys()) ?*/}"
  /*? open_proof ?*/rule subset_antisym/*? A ?*/
   /*? a ?*/clarsimp simp:dom_def /*? name ?*/_def/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/(rule conjI, simp add:dom_def /*? name ?*/_def)+/*? A ?*/
  /*? a ?*/simp add:dom_def /*? name ?*/_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma /*? name ?*/_range: "ran /*? name ?*/ = {/*? ', '.join(data.values()) ?*/}"
  sorry
(** TPP: condense = False *)
/*- endif -*/
/*- endmacro -*/

/*- set data = {} -*/
/*- for label, objs in obj_space.labels.items() -*/
  /*- for o in objs -*/
    /*- do data.__setitem__('%s_id' % o.name, '\'\'%s\'\'' % label) -*/
  /*- endfor -*/
/*- endfor -*/
/*? emit_map('tag_of\'', data, 'cdl_object_id', 'tag') ?*/

(** TPP: condense = True *)
lemma tag_of':
/*- for label, objs in obj_space.labels.items() -*/
  /*- for o in objs -*/
  "tag_of' /*? o.name ?*/_id = Some ''/*? label ?*/''"
  /*- endfor -*/
/*- endfor -*/
  /*? open_proof ?*/auto simp:tag_of'_def CapDLSpec.ids/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set data = {} -*/
/*- for label, objs in obj_space.labels.items() -*/
  /*- for o in objs -*/
    /*- if not isinstance(o, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
      /*- do data.__setitem__('%s_id' % o.name, '\'\'%s\'\'' % label) -*/
    /*- endif -*/
  /*- endfor -*/
/*- endfor -*/
definition tag_of :: "cdl_object_id \<Rightarrow> tag option"
  where "tag_of \<equiv> tag_of' ++ [
   /*- for k, v in data.items() -*/
   /*? k ?*/ \<mapsto> /*? v ?*//*- if not loop.last -*/,/*- endif -*/
   /*- endfor -*/
   ]"
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma tag_of_tag_of':"tag_of = tag_of'"
  /*? open_proof ?*/clarsimp simp:tag_of_def tag_of' intro!:ext/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma tag_of:
/*- for label, objs in obj_space.labels.items() -*/
  /*- for o in objs -*/
  "tag_of /*? o.name ?*/_id = Some ''/*? label ?*/''"
  /*- endfor -*/
/*- endfor -*/
  /*? open_proof ?*/(subst tag_of_tag_of', simp add:tag_of')+/*? close_proof ?*/
(** TPP: condense = False *)

/*- set data = {} -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if obj.name is not none -*/
    /*- do data.__setitem__('\'\'%s\'\'' % obj.name, '%s_id' % obj.name) -*/
  /*- endif -*/
/*- endfor -*/
/*? emit_map('id_of\'', data, 'string', 'cdl_object_id') ?*/

(** TPP: condense = True *)
lemma id_of':
/*- for k, v in data.items() -*/
  "id_of' /*? k ?*/ = Some /*? v ?*/"
/*- endfor -*/
  /*? open_proof ?*/auto simp:id_of'_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True*)
/*- set data2 = {} -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if obj.name is not none and not isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
    /*- do data2.__setitem__('\'\'%s\'\'' % obj.name, '%s_id' % obj.name) -*/
  /*- endif -*/
/*- endfor -*/
definition id_of :: "string \<Rightarrow> cdl_object_id option"
  where "id_of \<equiv> id_of' ++ [
   /*- for k, v in data2.items() -*/
   /*? k ?*/ \<mapsto> /*? v ?*//*- if not loop.last -*/,/*- endif -*/
   /*- endfor -*/
   ]"
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma id_of_id_of':"id_of = id_of'"
  /*? open_proof ?*/clarsimp simp:id_of_def id_of' intro!:ext/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma id_of:
/*- for k, v in data.items() -*/
  "id_of /*? k ?*/ = Some /*? v ?*/"
/*- endfor -*/
  /*? open_proof ?*/auto simp:id_of_def id_of'/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
text {*
  A @{term tag} is a label in a CAmkES view of the system. These are component
  instance names or connection names. A @{term label} is similar, but for an
  information flow perspective on the system. The latter is formed from the
  former by mapping any @{term tag} that represents a connection name to the
  @{term label} of its receiving component instance. This is to match the way
  authority on endpoints works in the access control model.
*}
/*- set tag_to_label = {'\'\'%s\'\'' % garbage_tag:'\'\'%s\'\'' % garbage_tag, '\'\'%s\'\'' % irq_tag:'\'\'%s\'\'' % irq_tag} -*/
/*- for inst in composition.instances -*/
  /*- do tag_to_label.__setitem__('\'\'%s\'\'' % inst.name, '\'\'%s\'\'' % inst.name) -*/
/*- endfor -*/
/*- for conn in composition.connections -*/
  /*- do tag_to_label.__setitem__('\'\'%s\'\'' % conn.name, '\'\'%s\'\'' % conn.to_end.instance.name) -*/
/*- endfor -*/
/*? emit_map('tag_to_label', tag_to_label, 'tag', 'label') ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*? '\n'.join(textwrap.wrap('lemmas frame_defs = %s' % ' '.join(map(lambda('x: \'%s_def\' % x.name'), filter(lambda('x: isinstance(x, capdl.Frame)'), obj_space.spec.objs))), width=100, subsequent_indent='  ')) ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*? '\n'.join(textwrap.wrap('lemmas frame_ids = %s' % ' '.join(map(lambda('x: \'%s_id_def\' % x.name'), filter(lambda('x: isinstance(x, capdl.Frame)'), obj_space.spec.objs))), width=100, subsequent_indent='  ')) ?*/
(** TPP: condense = False *)

/*- if False -*/
(** TPP: condense = True *)
lemma ids_distinct': "inj_on id_of (dom id_of)"
lemma ids_distinct': "\<And>n m. \<exists>i. id_of n = Some i \<and> id_of m = Some i \<Longrightarrow> n = m"
  /*- set to_unfold = set(['id_of_def']) -*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none -*/
      /*- do to_unfold.add('%s_id_def' % obj.name) -*/
    /*- endif -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %sunfold %s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %sunfold ' % open_proof))) ?*/
  /*- for n in obj_space.spec.objs -*/
    /*- if n.name is not none -*/
  /*? a ?*/case_tac "n = ''/*? n.name ?*/''"/*? A ?*/
      /*- for m in obj_space.spec.objs -*/
        /*- if m.name is not none -*/
   /*? a ?*/case_tac "m = ''/*? m.name ?*/''"/*? A ?*/
        /*? a ?*/clarsimp/*? A ?*/
        /*- endif -*/
      /*- endfor -*/
   /*? a ?*/clarsimp/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/clarsimp/*? close_proof ?*/
(** TPP: condense = False *)
/*- endif -*/

(** TPP: condense = True *)
definition ipc_buffer :: "string \<Rightarrow> nat \<Rightarrow> cdl_object_id option"
  where "ipc_buffer name index \<equiv>
  /*- set tcbs = {} -*/
  /*- set to_unfold = set() -*/
  /*- for i in composition.instances -*/
    /*- do tcbs.__setitem__('%s_%d_0_control_%d_tcb' % (i.name, len(i.name), len('0_control')), (i.name, 0)) -*/
    /*- for index, inf in enumerate(i.type.provides + i.type.uses + i.type.emits + i.type.consumes + i.type.dataports) -*/
      /*- do tcbs.__setitem__('%s_%d_%s_%d_0000_tcb' % (i.name, len(i.name), inf.name, len(inf.name)), (i.name, index + 1)) -*/
    /*- endfor -*/
  /*- endfor -*/
  /*- for o in obj_space.spec.objs -*/
    /*- if o.name is not none and o.name in tcbs -*/
      if name = ''/*? tcbs[o.name][0] ?*/'' \<and> index = /*? tcbs[o.name][1] ?*/ then Some /*? o['ipc_buffer_slot'].referent.name ?*/_id else
      /*- do to_unfold.add('%s_id_def' % o['ipc_buffer_slot'].referent.name) -*/
    /*- endif -*/
  /*- endfor -*/
      None
  "
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma buffers_distinct':
  "\<And>n i m j. \<exists>f. ipc_buffer n i = Some f \<and> ipc_buffer m j = Some f \<Longrightarrow> n = m \<and> i = j"
  /*? open_proof ?*/auto simp:ipc_buffer_def /*? ' '.join(to_unfold) ?*/ split:split_if_asm/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
definition extra' :: cdl_heap
  where "extra' identifier \<equiv>
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
    if identifier = /*? obj.name ?*/_id then Some /*? obj.name ?*/ else
    /*- endif -*/
  /*- endfor -*/
    None"
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma extra_only_pds_pts_frames:
  "case extra' x of None \<Rightarrow> True
                  | Some (Types_D.PageDirectory _) \<Rightarrow> True
                  | Some (Types_D.PageTable _) \<Rightarrow> True
                  | Some (Types_D.Frame _) \<Rightarrow> True
                  | _ \<Rightarrow> False"
  /*? open_proof ?*/unfold extra'_def/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:/*? obj.name ?*/_def/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
interpretation Generator_CAMKES_CDL.cdl_translation ipc_buffer id_of "''/*? garbage_tag ?*/''" "''/*? irq_tag ?*/''"
  /*? open_proof ?*/unfold_locales/*? A ?*/
  /*? a ?*/simp add:buffers_distinct'/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma cnode_objects_distinct:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x))
     (cnode_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  /*? open_proof ?*/subst dom_map_of_conv_image_fst/*? A ?*/
  /*? a ?*/simp add:cnode_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def/*? A ?*/
  /*? a ?*/simp add:id_of_id_of' id_of' dom_def/*? A ?*/
  /*? a ?*/code_simp/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set to_unfold = set(('tcb_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def')) -*/
/*# During the proof of this lemma we'll need to unfold the definitions of all
 *# the component instances and their types.
 #*/
/*- for i in composition.instances -*/
  /*- do list(map(to_unfold.add, ('ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name))) -*/
/*- endfor -*/
lemma tcb_objects_distinct:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x))
     (tcb_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  /*? open_proof ?*/subst dom_map_of_conv_image_fst/*? A ?*/
/*? '\n'.join(textwrap.wrap(' '.join(to_unfold), width=100, initial_indent='  %ssimp add:' % a, subsequent_indent=' ' * len('  %ssimp add:' % a))) ?*//*? A ?*/
  /*? a ?*/simp add:id_of_id_of' id_of' dom_def/*? A ?*/
  /*? a ?*/code_simp/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set to_unfold = set(('ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'ep_objs_def')) -*/
/*# During the proof of this lemma we'll need to unfold the definitions of all
 *# the connections.
 #*/
/*- for c in composition.connections -*/
  /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
/*- endfor -*/
lemma ep_objects_distinct:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x))
     (ep_objs ArchSpec.assembly'))) \<inter> dom extra' = {}"
  /*? open_proof ?*/subst dom_map_of_conv_image_fst/*? A ?*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (a, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % a))) ?*/
  /*? a ?*/simp add:id_of_id_of' id_of' dom_def/*? A ?*/
  /*? a ?*/code_simp/*? close_proof ?*/
(** TPP: condense = False *)

lemma objects_distinct: "dom (cdl_objects (generate' ArchSpec.assembly')) \<inter> dom extra' = {}"
  /*? open_proof ?*/simp add:generate'_def obj_heap_def/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/simp add:cnode_objects_distinct/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/simp add:tcb_objects_distinct/*? A ?*/
  /*? a ?*/simp add:ep_objects_distinct/*? close_proof ?*/

lemma extra_is_valid: "valid_extra (generate' ArchSpec.assembly') extra'"
  by (simp add:valid_extra_def extra_only_pds_pts_frames objects_distinct)

definition irqs :: irqs
  where "irqs \<equiv> \<lparr>
    irqs_map = CapDLSpec.irqs,
    irqs_objects = CapDLSpec.empty_irq_objects\<rparr>"

(** TPP: condense = True *)
/*# The IRQs are represented as empty CNodes, inferred by the CapDL translator
 *# to directly follow the explicit objects. We can thus calculate their object
 *# IDs by counting the objects we have explicitly. We need to create
 *# definitions like this and the lunacy that follows to deal with scalability
 *# problems in Isabelle stemming from unfolding the CapDLSpec.irqs map.
 #*/
/*- set irq_ids = list(six.moves.range(len(obj_space.spec.objs), len(obj_space.spec.objs) + 256)) -*/
definition range_irqs :: "cdl_object_id set"
  where "range_irqs \<equiv> {x. x \<ge> /*? min(irq_ids) ?*/ \<and> x \<le> /*? max(irq_ids) ?*/}"
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs: "CapDLSpec.irqs x = ucast x + /*? min(irq_ids) ?*/"
  /*- for i in six.moves.range(256) -*/
  /*- if i == 0 -*//*? open_proof ?*//*- else -*//*? a ?*//*- endif -*/case_tac "x = /*? i ?*/", simp add:CapDLSpec.irqs_def/*? A ?*/
  /*- endfor -*/
  /*? a ?*/simp/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma range_irqs_eq: "range CapDLSpec.irqs = range_irqs"
  /*? open_proof ?*/subst full_SetCompr_eq[symmetric]/*? A ?*/
  /*? a ?*/subst irqs/*? A ?*/
  /*? a ?*/unfold range_irqs_def/*? A ?*/
  /*? a ?*/rule subset_antisym/*? A ?*/
   /*? a ?*/clarsimp/*? A ?*/
   /*? a ?*/rule conjI/*? A ?*/
    /*? a ?*/subst add.commute/*? A ?*/
    /*? a ?*/rule_tac x'="ucast (max_word::8 word)" in word_random/*? A ?*/
     /*? a ?*/clarsimp simp:max_word_def/*? A ?*/
    /*? a ?*/simp add:ucast_le_ucast_8_32/*? A ?*/
   /*? a ?*/word_bitwise/*? A ?*/
   /*? a ?*/unat_arith/*? A ?*/
  /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/rule_tac x="ucast (x - /*? min(irq_ids) ?*/)" in exI/*? A ?*/
  /*? a ?*/subst le_max_word_ucast_id/*? A ?*/
   /*? a ?*/clarsimp simp:max_word_def/*? A ?*/
   /*? a ?*/unat_arith/*? A ?*/
  /*? a ?*/clarsimp/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma range_irqs_exhaust:
  fixes x :: cdl_object_id
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('  shows "\\<lbrakk>%d \\<le> x; x \\<le> %d; %s\\<rbrakk> \\<Longrightarrow> P"' % (min(irq_ids), max(irq_ids), '; '.join(map(lambda('x: \'x \\\\<noteq> %d\' % x'), irq_ids)))), width=100, subsequent_indent=' ' * len('  shows "[')))) ?*/ /*# XXX: fix syntax highlighting: " #*/
  (* warning: takes a LONG time *)
  /*? open_proof ?*/(drule_tac x=x in le_step_down_word_2, assumption, simp+)+/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_cnodes:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (cnode_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
  /*? open_proof ?*/simp add:cnode_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def CapDLSpec.empty_irq_objects_def/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*- set to_unfold = set(('id_of_def', 'id_of\'')) -*/
  /*- for i in composition.instances -*/
    /*- do to_unfold.add('CapDLSpec.%s_cnode_id_def' % i.name) -*/
  /*- endfor -*/
  /*? a ?*/clarsimp simp:/*? ' '.join(to_unfold) ?*//*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_tcbs:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (tcb_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
  /*? open_proof ?*/simp add:tcb_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def CapDLSpec.empty_irq_objects_def/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*- set to_unfold = set(('id_of_def', 'id_of\'')) -*/
  /*- for i in composition.instances -*/
    /*- do to_unfold.add('CapDLSpec.%s_%d_0_control_%d_tcb_id_def' % (i.name, len(i.name), len('0_control'))) -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % i.name) -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % i.type.name) -*/
    /*- for inf in i.type.provides + i.type.consumes -*/
      /*- do to_unfold.add('CapDLSpec.%s_%d_%s_%d_0000_tcb_id_def' % (i.name, len(i.name), inf.name, len(inf.name))) -*/
    /*- endfor -*/
  /*- endfor -*/
  /*? a ?*/simp add:/*? ' '.join(to_unfold) ?*//*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_eps:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (ep_objs assembly')))
     \<inter> dom empty_irq_objects = {}"
  /*? open_proof ?*/simp add:ep_objs_def ArchSpec.assembly'_def ArchSpec.composition'_def CapDLSpec.empty_irq_objects_def/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*- set to_unfold = set(('id_of_def', 'id_of\'')) -*/
  /*- for c in composition.connections -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
    /*- if c.type.name == 'seL4RPC' -*/
      /*- do to_unfold.add('CapDLSpec.%s_ep_id_def' % c.name) -*/
    /*- elif c.type.name == 'seL4Notification' -*/
      /*- do to_unfold.add('CapDLSpec.%s_aep_id_def' % c.name) -*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp add:/*? ' '.join(to_unfold) ?*//*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct:
  "dom (cdl_objects (generate' assembly')) \<inter> {x. /*? min(irq_ids) ?*/ \<le> x \<and> x \<le> /*? max(irq_ids) ?*/} = {}"
  /*? open_proof ?*/simp add:generate'_def obj_heap_def/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/cut_tac irqs_dom_distinct_cnodes[unfolded empty_irq_objects_def]/*? A ?*/
   /*? a ?*/subst (asm) dom_expand/*? A ?*/
   /*? a ?*/assumption/*? A ?*/
  /*? a ?*/rule union_split/*? A ?*/
   /*? a ?*/cut_tac irqs_dom_distinct_tcbs[unfolded empty_irq_objects_def]/*? A ?*/
   /*? a ?*/subst (asm) dom_expand/*? A ?*/
   /*? a ?*/assumption/*? A ?*/
  /*? a ?*/cut_tac irqs_dom_distinct_eps[unfolded empty_irq_objects_def]/*? A ?*/
  /*? a ?*/subst (asm) dom_expand/*? A ?*/
  /*? a ?*/assumption/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_dom_distinct_extra: "dom extra' \<inter> {x. /*? min(irq_ids) ?*/ \<le> x \<and> x \<le> /*? max(irq_ids) ?*/} = {}"
  /*? open_proof ?*/rule disjointI/*? A ?*/
  /*? a ?*/rename_tac x y/*? A ?*/
  /*? a ?*/drule domD/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:extra'_def /*? obj.name ?*/_id_def/*? A ?*/
   /*? a ?*/(fastforce|unat_arith)/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp add:extra'_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irqs_is_valid: "valid_irqs (generate' ArchSpec.assembly') extra' irqs"
  /*? open_proof ?*/simp add:valid_irqs_def irqs_def CapDLSpec.empty_irq_objects_def/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/subst range_irqs_eq/*? A ?*/
   /*? a ?*/subst range_irqs_def/*? A ?*/
   /*? a ?*/rule refl/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/simp add:irqs_dom_distinct/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/simp add:irqs_dom_distinct_extra/*? A ?*/
  /*? a ?*/simp/*? A ?*/
  /*? a ?*/subst ran_expand/*? A ?*/
   /*? a ?*/rule exI, force/*? A ?*/
  /*? a ?*/simp add:CapDLSpec.empty_irq_node_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma extra'_def2:
  "extra' = (\<lambda>x.
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none and isinstance(obj, (capdl.Frame, capdl.PageTable, capdl.PageDirectory)) -*/
    if x = /*? obj.name ?*/_id then Some /*? obj.name ?*/ else
    /*- endif -*/
  /*- endfor -*/
    None)"
  /*? open_proof ?*/rule ext/*? A ?*/
  /*? a ?*/simp add:extra'_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma dom_tcbs:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (tcb_objs ArchSpec.assembly'))) =
/*- set ids = set() -*/
/*- set to_unfold = set(('tcb_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def')) -*/
/*- for i in composition.instances -*/
  /*- do ids.add('%s_%d_0_control_%d_tcb_id' % (i.name, len(i.name), len('0_control'))) -*/
  /*- do list(map(to_unfold.add, ('ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name))) -*/
  /*- for inf in i.type.provides + i.type.consumes -*/
    /*- do ids.add('%s_%d_%s_%d_0000_tcb_id' % (i.name, len(i.name), inf.name, len(inf.name))) -*/
  /*- endfor -*/
/*- endfor -*/
/*? '\n'.join(textwrap.wrap('     {%s}"' % ', '.join(ids), width=100, subsequent_indent='      ')) ?*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %s' % open_proof))) ?*/
  /*? a ?*/simp add:id_of_def id_of'/*? close_proof ?*/
(** TPP: condense = False *)

/*- for i in composition.instances -*/
(** TPP: condense = True *)
lemma caps_of_/*? i.name ?*/: "cap_map ArchSpec.assembly' ''/*? i.name ?*/'' = CapDLSpec./*? i.name ?*/_cnode_caps"
  /*- set to_unfold = set(('cap_map_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name, 'CapDLSpec.%s_cnode_caps_def' % i.name, 'cap_offset_def', 'ep_objs_def')) -*/
  /*- for c in composition.connections -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*? a ?*/simp add:id_of_def id_of'/*? close_proof ?*/
(** TPP: condense = False *)
/*- endfor -*/

(** TPP: condense = True *)
/*- for i in composition.instances -*/

  /*# Find the CNode of this instance. We'll need this later on. #*/
  /*- set cnode_regex = re.compile('(?P<instance>[a-zA-Z_]\\w*)_cnode$') -*/
  /*- set cnode = [] -*/
  /*- for obj in obj_space.spec.objs -*/
    /*- if obj.name is not none -*/
      /*- set inst = cnode_regex.match(obj.name) -*/
      /*- if inst is not none -*/
        /*- do cnode.append(obj) -*/
        /*- break -*/
      /*- endif -*/
    /*- endif -*/
  /*- endfor -*/
  /*- if len(cnode) == 0 -*/
    /*? raise(TemplateError('failed to find CNode for TCB %s_%d_0_control_%d_tcb' % (i.name, len(i.name), len('0_control')))) ?*/
  /*- endif -*/
  /*- set cnode_size = capdl.calculate_cnode_size(max(cnode[0].slots.keys())) -*/

lemma cnode_size_of_/*? i.name ?*/: "cnode_size_bits ArchSpec.assembly' ''/*? i.name ?*/'' = /*? cnode_size ?*/"
  /*- set to_unfold = set(('cnode_size_bits_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'cap_map_def', 'cap_offset_def', 'ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name, 'ep_objs_def')) -*/
  /*- for c in composition.connections -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*? a ?*/rule Least/*? cnode_size ?*//*? A ?*/
  /*- for x in six.moves.range(0, cnode_size + 1) -*/
    /*- if loop.last -*/
  /*? a ?*/simp/*? close_proof ?*/
    /*- else -*/
  /*? ' ' * (cnode_size - x) ?*//*? a ?*/simp/*? A ?*/
    /*- endif -*/
  /*- endfor -*/

lemma tcb_of_/*? i.name ?*/_/*? len(i.name) ?*/_0_control_/*? len('0_control') ?*/_tcb:
  "map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (tcb_objs ArchSpec.assembly')) CapDLSpec./*? i.name ?*/_/*? len(i.name) ?*/_0_control_/*? len('0_control') ?*/_tcb_id
     = Some CapDLSpec./*? i.name ?*/_/*? len(i.name) ?*/_0_control_/*? len('0_control') ?*/_tcb"
  /*? open_proof ?*/simp add:tcb_objs_def/*? A ?*/
  /*- set to_unfold = set(['ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of', 'CapDLSpec.%s_%d_0_control_%d_tcb_def' % (i.name, len(i.name), len('0_control')), 'CapDLSpec.%s_%d_0_control_%d_tcb_caps_def' % (i.name, len(i.name), len('0_control'))]) -*/
  /*- for inst in composition.instances -*/
    /*- do list(map(to_unfold.add, ('ArchSpec.%s_def' % inst.name, 'ArchSpec.%s_def' % inst.type.name, 'CapDLSpec.%s_%d_0_control_%d_tcb_id_def' % (inst.name, len(inst.name), len('0_control'))))) -*/
    /*- for iface in inst.type.provides + inst.type.consumes -*/
      /*- do to_unfold.add('CapDLSpec.%s_%d_%s_%d_0000_tcb_id_def' % (inst.name, len(inst.name), iface.name, len(iface.name))) -*/
    /*- endfor -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (a, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % a))) ?*/
  /*? a ?*/rule all_ext/*? A ?*/
  /*? a ?*/rule allI/*? A ?*/
  /*? a ?*/case_tac "x = cspace"/*? A ?*/
   /*? a ?*/simp add:cspace_def vspace_def ipc_buffer_slot_def/*? A ?*/
   /*? a ?*/rule conjI2/*? A ?*/
    /*? a ?*/rule conjI2/*? A ?*/
  /*- set to_unfold = set(('cnode_size_bits_def', 'cap_map_def', 'cap_offset_def', 'ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name, 'ep_objs_def')) -*/
  /*- for c in composition.connections -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('    %ssimp add:%s%s' % (a, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('    %ssimp add:' % a))) ?*/
     /*? a ?*/(rule Least/*? cnode_size ?*/; clarsimp)/*? A ?*/
    /*? a ?*/simp add:cnode_guard_size_def/*? A ?*/
   /*? a ?*/simp add:cnode_guard_def/*? A ?*/
  /*? a ?*/simp add:cspace_def vspace_def ipc_buffer_slot_def ipc_buffer_def/*? close_proof ?*/

  /*- for inf in i.type.provides + i.type.consumes -*/

lemma tcb_of_/*? i.name ?*/_/*? len(i.name) ?*/_/*? inf.name ?*/_/*? len(inf.name) ?*/_0000_tcb:
  "map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (tcb_objs ArchSpec.assembly')) CapDLSpec./*? i.name ?*/_/*? len(i.name) ?*/_/*? inf.name ?*/_/*? len(inf.name) ?*/_0000_tcb_id
     = Some CapDLSpec./*? i.name ?*/_/*? len(i.name) ?*/_/*? inf.name ?*/_/*? len(inf.name) ?*/_0000_tcb"
  /*? open_proof ?*/simp add:tcb_objs_def/*? A ?*/
  /*- set to_unfold = set(['ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of', 'CapDLSpec.%s_%d_%s_%d_0000_tcb_def' % (i.name, len(i.name), inf.name, len(inf.name)), 'CapDLSpec.%s_%d_%s_%d_0000_tcb_caps_def' % (i.name, len(i.name), inf.name, len(inf.name))]) -*/
  /*- for inst in composition.instances -*/
    /*- do list(map(to_unfold.add, ('ArchSpec.%s_def' % inst.name, 'ArchSpec.%s_def' % inst.type.name, 'CapDLSpec.%s_%d_0_control_%d_tcb_id_def' % (inst.name, len(inst.name), len('0_control'))))) -*/
    /*- for iface in inst.type.provides + inst.type.consumes -*/
      /*- do to_unfold.add('CapDLSpec.%s_%d_%s_%d_0000_tcb_id_def' % (inst.name, len(inst.name), iface.name, len(iface.name))) -*/
    /*- endfor -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (a, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('  %ssimp add:' % a))) ?*/
  /*? a ?*/rule all_ext/*? A ?*/
  /*? a ?*/rule allI/*? A ?*/
  /*? a ?*/case_tac "x = cspace"/*? A ?*/
   /*? a ?*/simp add:cspace_def vspace_def ipc_buffer_slot_def/*? A ?*/
   /*? a ?*/rule conjI2/*? A ?*/
    /*? a ?*/rule conjI2/*? A ?*/
  /*- set to_unfold = set(('cnode_size_bits_def', 'cap_map_def', 'cap_offset_def', 'ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name, 'ep_objs_def')) -*/
  /*- for c in composition.connections -*/
    /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('    %ssimp add:%s%s' % (a, ' '.join(to_unfold), A), width=100, subsequent_indent=' ' * len('    %ssimp add:' % a))) ?*/
     /*? a ?*/(rule Least/*? cnode_size ?*/; clarsimp)/*? A ?*/
    /*? a ?*/simp add:cnode_guard_size_def/*? A ?*/
   /*? a ?*/simp add:cnode_guard_def/*? A ?*/
  /*? a ?*/simp add:cspace_def vspace_def ipc_buffer_slot_def ipc_buffer_def/*? close_proof ?*/

  /*- endfor -*/

/*- endfor -*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma dom_cnodes:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (cnode_objs ArchSpec.assembly'))) =
/*- set ids = set() -*/
/*- set to_unfold = set(('cnode_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of', 'instance_names_def')) -*/
/*- for i in composition.instances -*/
  /*- do ids.add('%s_cnode_id' % i.name) -*/
  /*- do list(map(to_unfold.add, ('ArchSpec.%s_def' % i.name, 'ArchSpec.%s_def' % i.type.name))) -*/
/*- endfor -*/
/*? '\n'.join(textwrap.wrap('     {%s}"' % ', '.join(ids), width=100, subsequent_indent='      ')) ?*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), close_proof), width=100, subsequent_indent=' ' * len('  %s' % open_proof))) ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- for i in composition.instances -*/
lemma cnode_of_/*? i.name ?*/_cnode:
  "map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (cnode_objs ArchSpec.assembly')) CapDLSpec./*? i.name ?*/_cnode_id
     = Some CapDLSpec./*? i.name ?*/_cnode"
  /*? open_proof ?*/cut_tac caps_of_/*? i.name ?*//*? A ?*/
  /*? a ?*/cut_tac cnode_size_of_/*? i.name ?*//*? A ?*/
  /*- set to_unfold = set(('cnode_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of', 'instance_names_def', 'CapDLSpec.%s_cnode_def' % i.name)) -*/
  /*- for i2 in composition.instances -*/
    /*- do to_unfold.add('CapDLSpec.%s_cnode_id_def' % i2.name) -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (a, ' '.join(to_unfold), close_proof), width=100, subsequent_indent=' ' * len('  %ssimp add:' % a))) ?*/
/*- endfor -*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma dom_eps:
  "dom (map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (ep_objs ArchSpec.assembly'))) =
/*- set ids = set() -*/
/*- set to_unfold = set(('ep_objs_def', 'ArchSpec.assembly\'_def', 'ArchSpec.composition\'_def', 'id_of')) -*/
/*- for c in composition.connections -*/
  /*- if c.type.name == 'seL4RPC' -*/
    /*- do ids.add('%s_ep_id' % c.name) -*/
  /*- elif c.type.name == 'seL4Notification' -*/
    /*- do ids.add('%s_aep_id' % c.name) -*/
  /*- endif -*/
  /*- do to_unfold.add('ArchSpec.%s_def' % c.name) -*/
/*- endfor -*/
/*? '\n'.join(textwrap.wrap('     {%s}"' % ', '.join(ids), width=100, subsequent_indent='      ')) ?*/
/*? '\n'.join(textwrap.wrap('  %ssimp add:%s%s' % (open_proof, ' '.join(to_unfold), close_proof), width=100, subsequent_indent=' ' * len('  %s' % open_proof))) ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- for c in composition.connections -*/
  /*- if c.type.name == 'seL4RPC' -*/
lemma ep_of_/*? c.name ?*/_ep:
  "map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (ep_objs ArchSpec.assembly')) CapDLSpec./*? c.name ?*/_ep_id
     = Some CapDLSpec./*? c.name ?*/_ep"
/*? '\n'.join(textwrap.wrap('  %ssimp add:ep_objs_def ArchSpec.assembly\'_def ArchSpec.composition\'_def ArchSpec.%s_def id_of CapDLSpec.%s_ep_def%s' % (open_proof, c.name, c.name, close_proof), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*- elif c.type.name == 'seL4Notification' -*/
lemma ep_of_/*? c.name ?*/_aep:
  "map_of (map (\<lambda>x. (the (id_of (cdlo_name x)), cdlo_type x)) (ep_objs ArchSpec.assembly')) CapDLSpec./*? c.name ?*/_aep_id
     = Some CapDLSpec./*? c.name ?*/_aep"
/*? '\n'.join(textwrap.wrap('  %ssimp add:ep_objs_def ArchSpec.assembly\'_def ArchSpec.composition\'_def ArchSpec.%s_def id_of CapDLSpec.%s_aep_def%s' % (open_proof, c.name, c.name, close_proof), width=100, subsequent_indent=' ' * len('  %ssimp add:' % open_proof))) ?*/
  /*- endif -*/
/*- endfor -*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma dom_objects:
/*- set ids = set() -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if obj.name is not none -*/
    /*- do ids.add('CapDLSpec.%s_id' % obj.name) -*/
  /*- endif -*/
/*- endfor -*/
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('  "dom CapDLSpec.objects = {%s} \\<union> dom CapDLSpec.empty_irq_objects"' % ', '.join(ids)), width=100, subsequent_indent=' ' * len('  "dom objects = {')))) ?*/ /*# XXX: fix syntax highlighting: " #*/
  /*? open_proof ?*/unfold CapDLSpec.objects_def/*? A ?*/
  /*? a ?*/(subst map_add_assoc[symmetric])+/*? A ?*/
  /*? a ?*/rule dom_map_add/*? A ?*/
  /*? a ?*/simp add:CapDLSpec.ids/*? A ?*/
  /*? a ?*/(subst dom_expand)+/*? A ?*/
  /*? a ?*/rule subset_antisym/*? A ?*/
   /*? a ?*/(subst insert_subset,
          rule conjI,
           (subst insert_strip, (simp; fail))+,
           (subst insertI1, (simp; fail)))+/*? A ?*/
   /*? a ?*/rule Un_least/*? A ?*/
    /*? a ?*/subst set_compre_unwrap/*? A ?*/
    /*? a ?*/unat_arith/*? A ?*/
   /*? a ?*/subst set_compre_unwrap/*? A ?*/
   /*? a ?*/unat_arith/*? A ?*/
  /*? a ?*/subst subset_eq/*? A ?*/
  /*? a ?*/rule ballI/*? A ?*/
  /*? a ?*/rename_tac x/*? A ?*/
  /*- set to_unfold = set() -*/
  /*- for o in obj_space.spec.objs -*/
  /*? a ?*/case_tac "x = /*? o.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:/*? o.name ?*/_id_def/*? A ?*/
    /*- do to_unfold.add('%s_id_def' % o.name) -*/
  /*- endfor -*/
  /*? a ?*/simp add:/*? ' '.join(to_unfold) ?*//*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma irq_at: "\<lbrakk>x \<ge> /*? min(irq_ids) ?*/; x \<le> /*? max(irq_ids) ?*/\<rbrakk> \<Longrightarrow> CapDLSpec.objects x = Some CapDLSpec.empty_irq_node"
  /*? open_proof ?*/unfold CapDLSpec.objects_def/*? A ?*/
  /*? a ?*/subst map_add_dom_app_simps(3)/*? A ?*/
   /*? a ?*/simp add:frame_ids/*? A ?*/
   /*? a ?*/unat_arith/*? A ?*/
  /*? a ?*/(subst map_add_dom_app_simps(3),
   /*? ' ' * len(a) ?*/simp add:frame_ids,
   /*? ' ' * len(a) ?*/unat_arith)+/*? A ?*/
  /*? a ?*/simp add:CapDLSpec.empty_irq_objects_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma objects_eq:
  "irqs_objects irqs ++ extra' ++ cdl_objects (generate' assembly') = CapDLSpec.objects"
  /*? open_proof ?*/unfold CapDLSpec.objects_def CapDLLabels.irqs_def/*? A ?*/
  /*? a ?*/(subst map_add_assoc[symmetric])+/*? A ?*/
  /*? a ?*/rule map_add_same/*? A ?*/
   /*? a ?*//*? solve_with('simp') ?*//*? A ?*/
  /*? a ?*/simp add:generate'_def/*? A ?*/
  /*? a ?*/rule ext/*? A ?*/
  /*? a ?*/rename_tac x/*? A ?*/
  /*? a ?*/unfold obj_heap_def2/*? A ?*/
  /*- for o in obj_space.spec.objs -*/
    /*- if not isinstance(o, capdl.Frame) -*/
  /*? a ?*/case_tac "x = /*? o.name ?*/_id"/*? A ?*/
      /*- if isinstance(o, capdl.CNode) -*/
   (* This thing is a CNode *)
   /*? a ?*/subst map_add_find_right[where xx=/*? o.name ?*/]/*? A ?*/
    /*? a ?*//*? solve_with('simp add:cnode_of_%s' % o.name) ?*//*? A ?*/
   /*? a ?*//*? solve_with('simp add:ids') ?*//*? A ?*/
      /*- elif isinstance(o, capdl.TCB) -*/
   (* This thing is a TCB *)
   /*? a ?*/subst map_add_find_right[where xx=/*? o.name ?*/]/*? A ?*/
    /*? a ?*/subst map_add_find_left/*? A ?*/
     /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
     /*? a ?*//*? solve_with('simp add:dom_cnodes ids') ?*//*? A ?*/
    /*? a ?*/subst map_add_find_right[where xx=/*? o.name ?*/]/*? A ?*/
     /*? a ?*//*? solve_with('simp add:tcb_of_%s' % o.name) ?*//*? A ?*/
    /*? a ?*//*? solve_with('rule refl') ?*//*? A ?*/
   /*? a ?*//*? solve_with('simp add:ids') ?*//*? A ?*/
      /*- elif isinstance(o, (capdl.Endpoint, capdl.AsyncEndpoint)) -*/
   (* This thing is an endpoint *)
   /*? a ?*/subst map_add_find_right[where xx=/*? o.name ?*/]/*? A ?*/
    /*? a ?*/subst map_add_find_left/*? A ?*/
     /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
     /*? a ?*//*? solve_with('simp add:dom_cnodes ids') ?*//*? A ?*/
    /*? a ?*/subst map_add_find_left/*? A ?*/
     /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
     /*? a ?*//*? solve_with('simp add:dom_tcbs ids') ?*//*? A ?*/
    /*? a ?*//*? solve_with('simp add:ep_of_%s' % o.name) ?*//*? A ?*/
   /*? a ?*//*? solve_with('simp add:ids') ?*//*? A ?*/
      /*- else -*/
  (* This thing is an address space object *)
   /*? a ?*/subst map_add_find_left/*? A ?*/
    /*? a ?*/subst map_add_find_left/*? A ?*/
     /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
     /*? a ?*//*? solve_with('simp add:dom_cnodes ids') ?*//*? A ?*/
    /*? a ?*/subst map_add_find_left/*? A ?*/
     /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
     /*? a ?*//*? solve_with('simp add:dom_tcbs ids') ?*//*? A ?*/
    /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
    /*? a ?*//*? solve_with('simp add:dom_eps ids') ?*//*? A ?*/
   /*? a ?*//*? solve_with('simp add:extra\'_def ids') ?*//*? A ?*/
      /*- endif -*/
    /*- endif -*/
  /*- endfor -*/
  (* Now we should only have the frames left to deal with *)
  /*? a ?*/subst map_add_find_left/*? A ?*/
   /*? a ?*/subst map_add_find_left/*? A ?*/
    /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
    /*? a ?*//*? solve_with('simp add:dom_cnodes ids') ?*//*? A ?*/
   /*? a ?*/subst map_add_find_left/*? A ?*/
    /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
    /*? a ?*//*? solve_with('simp add:dom_tcbs ids') ?*//*? A ?*/
   /*? a ?*/rule_tac x=x in not_in_domD/*? A ?*/
   /*? a ?*//*? solve_with('simp add:dom_eps ids') ?*//*? A ?*/
  /*- for o in obj_space.spec.objs -*/
    /*- if isinstance(o, capdl.Frame) -*/
  /*? a ?*/case_tac "x = /*? o.name ?*/_id"/*? A ?*/
   /*? a ?*//*? solve_with('simp add:ids extra\'_def map_add_def frame_defs; unat_arith?') ?*//*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/simp add:ids extra'_def map_add_def/*? A ?*/
  /*? a ?*/unat_arith?/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma spec_generation_correct:
  "generate ArchSpec.assembly' extra' irqs = Some (s, ps) \<Longrightarrow> s = CapDLSpec.state"
  /*? open_proof ?*/simp add:generate_def split:split_case_asm/*? A ?*/
  /*? a ?*/simp add:state_of_def merge_objs_def CapDLSpec.state_def merge_cdl_def split:split_if_asm/*? A ?*/
  /*? a ?*/(rule cdl_state.equality; clarsimp)/*? A ?*/
        /*? a ?*/simp add:generate'_def/*? A ?*/
       /*? a ?*/rule objects_eq/*? A ?*/
      /*? a ?*/simp add:generate'_def CapDLSpec.cdt_def/*? A ?*/
     /*? a ?*/simp add:generate'_def/*? A ?*/
    /*? a ?*/simp add:CapDLLabels.irqs_def/*? A ?*/
   /*? a ?*/simp add:generate'_def CapDLSpec.asid_table_def/*? A ?*/
  /*? a ?*/simp add:generate'_def/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
/*# Construct a set of edges that comprise an authority graph for this system.
 #*/
/*- set edges = set() -*/

/*# All the possible authority types. See `auth` in Access.thy. #*/
/*- set datatype_auth = ('Control', 'Receive', 'SyncSend', 'AsyncSend', 'Reset', 'Grant', 'Write', 'Read', 'ASIDPoolMapsASID') -*/

/*# A wellformed policy must have edges allowing every label full control over
 *# itself.
 #*/
/*- for tag in tag_to_label -*/
  /*- for auth in datatype_auth -*/
    /*- do edges.add((tag, auth, tag)) -*/
  /*- endfor -*/
/*- endfor -*/

/*# The connections between components imply different categories of authority
 *# between those components. Below, the types of capabilities that each type
 *# of connection creates is implicit, but the rules for mapping capabilities
 *# to authorities are lifted from Dpolicy.thy.
 #*/
/*- for c in composition.connections -*/
  /*? assert(len(c.from_ends) == 1) ?*/
  /*? assert(len(c.to_ends) == 1) ?*/
  /*? assert('\'\'%s\'\'' % c.from_end.instance.name in tag_to_label) ?*/
  /*? assert('\'\'%s\'\'' % c.name in tag_to_label) ?*/
  /*? assert('\'\'%s\'\'' % c.to_end.instance.name in tag_to_label) ?*/
  /*- if c.type.name == 'seL4RPC' -*/
    /*- for auth in ('Receive', 'Reset', 'SyncSend') -*/
      /*- do edges.add(('\'\'%s\'\'' % c.from_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
    /*- for auth in ('Receive', 'Reset', 'SyncSend') -*/
      /*- do edges.add(('\'\'%s\'\'' % c.to_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
  /*- elif c.type.name == 'seL4Notification' -*/
    /*- for auth in ('AsyncSend', 'Reset') -*/
      /*- do edges.add(('\'\'%s\'\'' % c.from_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
    /*- for auth in ('Receive', 'Reset') -*/
      /*- do edges.add(('\'\'%s\'\'' % c.to_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
  /*- elif c.type.name == 'seL4RPCCall' -*/
    /*- for auth in datatype_auth -*/
      /*- do edges.add(('\'\'%s\'\'' % c.from_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
    /*- for auth in ('Receive', 'Reset', 'SyncSend') -*/
      /*- do edges.add(('\'\'%s\'\'' % c.to_end.instance.name, auth, '\'\'%s\'\'' % c.name)) -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/

definition tag_policy :: "tag auth_graph"
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('  where "tag_policy \\<equiv> {%s}"' % ', '.join(map(lambda('x: \'(%s, %s, %s)\' % x'), edges))), width=100, subsequent_indent=' ' * len('  where "tag_policy = {')))) ?*/ /*# XXX: fix syntax highlighting: " #*/
(** TPP: condense = False *)

(** TPP: condense = True *)
definition label_policy :: "label auth_graph"
/*- set label_edges = set() -*/
/*- for edge in edges -*/
  /*- do label_edges.add((tag_to_label[edge[0]], edge[1], tag_to_label[edge[2]])) -*/
/*- endfor -*/
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('  where "label_policy \\<equiv> {%s}"' % ', '.join(map(lambda('x: \'(%s, %s, %s)\' % x'), label_edges))), width=100, subsequent_indent=' ' * len('  where "label_policy = {')))) ?*/ /*# XXX: fix syntax highlighting: " #*/
(** TPP: condense = False *)

definition irq_label :: label
  where "irq_label \<equiv> ''/*? irq_tag ?*/''"

lemma concrete_policy_wf: "\<forall>agent. policy_wellformed label_policy False {irq_label} agent"
  /*? open_proof ?*/simp add:policy_wellformed_def label_policy_def/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/rule allI/*? A ?*/
   /*? a ?*/rule allI/*? A ?*/
   /*? a ?*/(case_tac agent, (case_tac a, simp+)+)[1]/*? A ?*/
  /*? a ?*/rule allI/*? A ?*/
  /*? a ?*/rule allI/*? A ?*/
  /*? a ?*/rule impI/*? A ?*/
  /*? a ?*/rule conjI/*? A ?*/
   /*? a ?*/(case_tac s, (case_tac r, simp+)+)[1]/*? A ?*/
  /*? a ?*/(case_tac s, (case_tac r, simp+)+)[1]/*? close_proof ?*/

definition label_of :: "cdl_object_id \<Rightarrow> label"
  where "label_of ident \<equiv> the (tag_to_label (the (tag_of ident)))"

definition valid_pas :: "label PAS \<Rightarrow> bool"
  where "valid_pas pas \<equiv>
           (\<forall>irq. pasObjectAbs pas (cdl_irq_node CapDLSpec.state irq) = irq_label) \<and>
           pasObjectAbs pas = label_of \<and>
           pasIRQAbs pas = (\<lambda>_. irq_label) \<and>
           pasPolicy pas = label_policy \<and>
           \<not> pasMayActivate pas \<and>
           \<not> pasMayEditReadyQueues pas \<and>
           \<not> pasMaySendIrqs pas"

lemma valid_pas_to_policy: "valid_pas pas \<Longrightarrow> pasPolicy pas = label_policy"
  /*? open_proof ?*/simp add:valid_pas_def/*? close_proof ?*/

lemma irqs_range_pas: "valid_pas pas \<Longrightarrow> range (pasIRQAbs pas) = {irq_label}"
  /*? open_proof ?*/clarsimp simp:valid_pas_def/*? close_proof ?*/

lemma valid_pas_to_label_of: "valid_pas pas \<Longrightarrow> pasObjectAbs pas = label_of"
  /*? open_proof ?*/clarsimp simp:valid_pas_def/*? close_proof ?*/

lemma tcb_ids:
  "objects obj_id = Some (Types_D.Tcb tcb) \<Longrightarrow> obj_id \<in> {/*? ', '.join(map(lambda('x: \'%s_id\' % x.name'), filter(lambda('x: isinstance(x, capdl.TCB)'), obj_space.spec.objs))) ?*/}"
  /*? open_proof ?*/clarsimp simp:objects_def ids obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/

lemma cnode_ids:
  "objects obj_id = Some (Types_D.CNode cnode) \<Longrightarrow> obj_id \<in> {/*? ', '.join(map(lambda('x: \'%s_id\' % x.name'), filter(lambda('x: isinstance(x, capdl.CNode)'), obj_space.spec.objs))) ?*/}"
  /*? open_proof ?*/clarsimp simp:objects_def ids obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/

lemma asid_ids:
  "objects obj_id = Some (Types_D.AsidPool asid) \<Longrightarrow> obj_id \<in> {}"
  /*? open_proof ?*/clarsimp simp:objects_def ids obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/

lemma pt_ids:
  "objects obj_id = Some (Types_D.PageTable pt) \<Longrightarrow> obj_id \<in> {/*? ', '.join(map(lambda('x: \'%s_id\' % x.name'), filter(lambda('x: isinstance(x, capdl.PageTable)'), obj_space.spec.objs))) ?*/}"
  /*? open_proof ?*/clarsimp simp:objects_def ids obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/

lemma pd_ids:
  "objects obj_id = Some (Types_D.PageDirectory pd) \<Longrightarrow> obj_id \<in> {/*? ', '.join(map(lambda('x: \'%s_id\' % x.name'), filter(lambda('x: isinstance(x, capdl.PageDirectory)'), obj_space.spec.objs))) ?*/}"
  /*? open_proof ?*/clarsimp simp:objects_def ids obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/

(** TPP: condense = True *)
lemma only_ep_caps:
  "\<lbrakk>opt_cap x CapDLSpec.state = Some cap;
    case CapDLSpec.objects (fst x) of Some (Types_D.CNode _) \<Rightarrow> True | _ \<Rightarrow> False\<rbrakk> \<Longrightarrow>
     case cap of Types_D.EndpointCap _ _ _ \<Rightarrow> True
               | Types_D.AsyncEndpointCap _ _ _ \<Rightarrow> True
               | _ \<Rightarrow> False"
  /*? open_proof ?*/clarsimp simp:opt_cap_def slots_of_def opt_object_def CapDLSpec.state_def object_slots_def/*? A ?*/
  /*? a ?*/case_tac x; clarsimp/*? A ?*/
  /*? a ?*/rename_tac obj_id slot/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
  /*? a ?*/case_tac "obj_id = /*? obj.name ?*/_id"/*? A ?*/
    /*- if isinstance(obj, capdl.CNode) -*/
   /*? a ?*/clarsimp simp:CapDLSpec.objects /*? obj.name ?*/_def /*? obj.name ?*/_caps_def split:split_if_asm/*? A ?*/
    /*- else -*/
   /*? a ?*/clarsimp simp:CapDLSpec.objects /*? obj.name ?*/_def split:split_if_asm/*? A ?*/
    /*- endif -*/
  /*- endfor -*/
  /*? a ?*/case_tac "CapDLSpec.objects obj_id = Some CapDLSpec.empty_irq_node"/*? A ?*/
   /*? a ?*/clarsimp simp:CapDLSpec.empty_irq_node_def/*? A ?*/
  /*? a ?*/clarsimp simp:CapDLSpec.objects_def CapDLSpec.empty_irq_objects_def split:split_if_asm/*? close_proof ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma only_certain_caps:
  "opt_cap x CapDLSpec.state = Some cap \<Longrightarrow>
     case cap of Types_D.EndpointCap _ _ _ \<Rightarrow> True
               | Types_D.AsyncEndpointCap _ _ _ \<Rightarrow> True
               | Types_D.CNodeCap _ _ _ _ \<Rightarrow> True
               | Types_D.FrameCap _ _ _ _ _ \<Rightarrow> True
               | Types_D.PageTableCap _ _ _ \<Rightarrow> True
               | Types_D.PageDirectoryCap _ _ _ \<Rightarrow> True
               | _ \<Rightarrow> False"
  /*? open_proof ?*/clarsimp simp:opt_cap_def slots_of_def object_slots_def opt_object_def CapDLSpec.state_def
                 split:split_pair_asm split_case_asm/*? A ?*/
  /*? a ?*/rename_tac obj_id slot obj/*? A ?*/
  /*? a ?*/case_tac obj; clarsimp/*? A ?*/
       /*? a ?*/rename_tac tcb/*? A ?*/
       /*? a ?*/frule tcb_ids/*? A ?*/
       /*- for o in obj_space.spec.objs -*/
         /*- if isinstance(o, capdl.TCB) -*/
       /*? a ?*/case_tac "obj_id = /*? o.name ?*/_id"/*? A ?*/
        /*? a ?*/clarsimp simp:objects obj_defs /*? o.name ?*/_caps_def split:split_if_asm/*? A ?*/
         /*- endif -*/
       /*- endfor -*/
       /*? a ?*/clarsimp/*? A ?*/
      /*? a ?*/rename_tac cnode/*? A ?*/
      /*? a ?*/frule cnode_ids/*? A ?*/
      /*- for o in obj_space.spec.objs -*/
        /*- if isinstance(o, capdl.CNode) -*/
      /*? a ?*/case_tac "obj_id = /*? o.name ?*/_id"/*? A ?*/
       /*? a ?*/clarsimp simp:objects obj_defs /*? o.name ?*/_caps_def split:split_if_asm/*? A ?*/
        /*- endif -*/
      /*- endfor -*/
      /*? a ?*/clarsimp/*? A ?*/
     /*? a ?*/rename_tac asid/*? A ?*/
     /*? a ?*/frule asid_ids/*? A ?*/
     /*? a ?*/clarsimp/*? A ?*/
    /*? a ?*/rename_tac pt/*? A ?*/
    /*? a ?*/frule pt_ids/*? A ?*/
    /*- for o in obj_space.spec.objs -*/
      /*- if isinstance(o, capdl.PageTable) -*/
    /*? a ?*/case_tac "obj_id = /*? o.name ?*/_id"/*? A ?*/
     /*? a ?*/clarsimp simp:objects obj_defs /*? o.name ?*/_caps_def split:split_if_asm/*? A ?*/
      /*- endif -*/
    /*- endfor -*/
    /*? a ?*/clarsimp/*? A ?*/
   /*? a ?*/rename_tac pd/*? A ?*/
   /*? a ?*/frule pd_ids/*? A ?*/
   /*- for o in obj_space.spec.objs -*/
     /*- if isinstance(o, capdl.PageDirectory) -*/
   /*? a ?*/case_tac "obj_id = /*? o.name ?*/_id"/*? A ?*/
    /*? a ?*/clarsimp simp:objects obj_defs /*? o.name ?*/_caps_def split:split_if_asm/*? A ?*/
     /*- endif -*/
   /*- endfor -*/
   /*? a ?*/clarsimp/*? A ?*/
  /*? a ?*/rename_tac irq/*? A ?*/
  /*? a ?*/clarsimp simp:objects_def obj_defs empty_irq_objects_def empty_irq_node_def split:split_if_asm/*? close_proof ?*/
(** TPP: condense = False *)

lemma no_asid_caps: "opt_cap x CapDLSpec.state = Some cap \<Longrightarrow>
                  case cap of Types_D.AsidPoolCap _ _ \<Rightarrow> False
                            | Types_D.AsidControlCap \<Rightarrow> False
                            | _ \<Rightarrow> True"
  /*? open_proof ?*/drule only_certain_caps/*? A ?*/
  /*? a ?*//*? solve_with('case_tac cap; clarsimp') ?*//*? close_proof ?*/

lemma no_irqs: "cdl_state_irqs_to_policy pas CapDLSpec.state = {}"
  apply (subst all_not_in_conv[symmetric])
  apply (rule allI)
  apply (case_tac x)
  apply (rename_tac a b c)
  apply (rule_tac ?a1.0=a and ?a2.0=b and ?a3.0=c and aag=pas in cdl_state_irqs_to_policy_aux.cases)
prefer 2
apply clarsimp
oops

(** TPP: condense = True *)
lemma which_ep:
  "\<lbrakk>opt_cap (x, b) state = Some cap; cap = (cdl_cap.EndpointCap obj badge rights)\<rbrakk> \<Longrightarrow>
/*- set caps = set() -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if isinstance(obj, capdl.CNode) -*/
    /*- for cap in obj.slots.values() -*/
      /*- if cap is not none and isinstance(cap.referent, capdl.Endpoint) -*/
        /*- do caps.add('Types_D.EndpointCap %s_id %s %s%s%s' % (cap.referent.name, cap.badge if cap.badge else '0', 'R' if cap.read else '', 'W' if cap.write else '', 'G' if cap.grant else '')) -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('    cap \\<in> {%s}"' % ', '.join(caps)), width=100, subsequent_indent=' ' * len(macros.isabelle_encode('    cap \\<in> {'))))) ?*/
  /*? open_proof ?*/clarsimp simp:CapDLSpec.state_def opt_cap_def slots_of_def opt_object_def/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
    /*- if obj.is_container() -*/
/*? '\n'.join(textwrap.wrap('   %sclarsimp simp:CapDLSpec.objects object_slots_def CapDLSpec.%s_def CapDLSpec.%s_caps_def split:split_if_asm%s' % (a, obj.name, obj.name, A), width=100, subsequent_indent=' ' * len('   %sclarsimp ' % a))) ?*/
    /*- else -*/
/*? '\n'.join(textwrap.wrap('   %sclarsimp simp:CapDLSpec.objects object_slots_def CapDLSpec.%s_def%s' % (a, obj.name, A), width=100, subsequent_indent=' ' * len('   %sclarsimp ' % a))) ?*/
    /*- endif -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %sclarsimp simp:CapDLSpec.objects_def CapDLSpec.objects CapDLSpec.empty_irq_objects_def CapDLSpec.empty_irq_node_def object_slots_def split:split_if_asm%s' % (a, close_proof), width=100, subsequent_indent=' ' * len('  %sclarsimp simp:' % a))) ?*/
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma which_aep:
  "\<lbrakk>opt_cap (x, b) state = Some cap; cap = (cdl_cap.AsyncEndpointCap obj badge rights)\<rbrakk> \<Longrightarrow>
/*- set caps = set() -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if isinstance(obj, capdl.CNode) -*/
    /*- for cap in obj.slots.values() -*/
      /*- if cap is not none and isinstance(cap.referent, capdl.AsyncEndpoint) -*/
        /*- do caps.add('Types_D.AsyncEndpointCap %s_id %s %s%s%s' % (cap.referent.name, cap.badge if cap.badge else '0', 'R' if cap.read else '', 'W' if cap.write else '', 'G' if cap.grant else '')) -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/
/*? '\n'.join(map(macros.isabelle_decode, textwrap.wrap(macros.isabelle_encode('    cap \\<in> {%s}"' % ', '.join(caps)), width=100, subsequent_indent=' ' * len(macros.isabelle_encode('    cap \\<in> {'))))) ?*/
  /*? open_proof ?*/clarsimp simp:CapDLSpec.state_def opt_cap_def slots_of_def opt_object_def/*? A ?*/
  /*- for obj in obj_space.spec.objs -*/
  /*? a ?*/case_tac "x = /*? obj.name ?*/_id"/*? A ?*/
    /*- if obj.is_container() -*/
/*? '\n'.join(textwrap.wrap('   %sclarsimp simp:CapDLSpec.objects object_slots_def CapDLSpec.%s_def CapDLSpec.%s_caps_def split:split_if_asm%s' % (a, obj.name, obj.name, A), width=100, subsequent_indent=' ' * len('   %sclarsimp ' % a))) ?*/
    /*- else -*/
/*? '\n'.join(textwrap.wrap('   %sclarsimp simp:CapDLSpec.objects object_slots_def CapDLSpec.%s_def%s' % (a, obj.name, A), width=100, subsequent_indent=' ' * len('   %sclarsimp ' % a))) ?*/
    /*- endif -*/
  /*- endfor -*/
/*? '\n'.join(textwrap.wrap('  %sclarsimp simp:CapDLSpec.objects_def CapDLSpec.objects CapDLSpec.empty_irq_objects_def CapDLSpec.empty_irq_node_def object_slots_def split:split_if_asm%s' % (a, close_proof), width=100, subsequent_indent=' ' * len('  %sclarsimp simp:' % a))) ?*/
(** TPP: condense = False *)

/*- if False -*/ /*# XXX: temporarily disable the policy stuff. #*/

/*# Construct the concrete authority graph. #*/
/*- set concrete_policy = set() -*/
/*- for subject in obj_space.spec.objs -*/
  /*- if subject.is_container() -*/
    /*- for cap in subject.slots.values() -*/
      /*# The following mimics the logic of `cap_auth_conferred` and `cap_rights_to_auth`. #*/
      /*- if cap is not none -*/
        /*- set object = cap.referent -*/
        /*- if isinstance(object, capdl.Endpoint) -*/
          /*- do concrete_policy.add((subject, 'Reset', object)) -*/
          /*- if cap.read -*/
            /*- do concrete_policy.add((subject, 'Receive', object)) -*/
          /*- endif -*/
          /*- if cap.write -*/
            /*- do concrete_policy.add((subject, 'SyncSend', object)) -*/
          /*- endif -*/
          /*- if cap.grant -*/
            /*- for auth in datatype_auth -*/
              /*- do concrete_policy.add((subject, auth, object)) -*/
            /*- endfor -*/
          /*- endif -*/
        /*- elif isinstance(object, capdl.AsyncEndpoint) -*/
          /*- do concrete_policy.add((subject, 'Reset', object)) -*/
          /*- if cap.read -*/
            /*- do concrete_policy.add((subject, 'Receive', object)) -*/
          /*- endif -*/
          /*- if cap.write -*/
            /*- do concrete_policy.add((subject, 'AsyncSyncSend', object)) -*/
          /*- endif -*/
        /*- elif isinstance(object, capdl.CNode) -*/
          /*- do concrete_policy.add((subject, 'Control', object)) -*/
        /*- elif isinstance(object, capdl.Frame) -*/
          /*- if cap.read -*/
            /*- do concrete_policy.add((subject, 'Read', object)) -*/
          /*- endif -*/
          /*- if cap.write -*/
            /*- do concrete_policy.add((subject, 'Write', object)) -*/
          /*- endif -*/
          /*- if cap.grant -*/
            /*- do concrete_policy.add((subject, 'Control', object)) -*/
          /*- endif -*/
        /*- elif isinstance(object, capdl.PageTable) -*/
          /*- do concrete_policy.add((subject, 'Control', object)) -*/
        /*- elif isinstance(object, capdl.PageDirectory) -*/
          /*- do concrete_policy.add((subject, 'Control', object)) -*/
        /*- else -*/
          /*? raise(TemplateError('unexpected cap type in CNode')) ?*/
        /*- endif -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/

definition concrete_policy :: "cdl_object_id auth_graph"
/*? '\n'.join(textwrap.wrap('  where "concrete_policy \\<equiv> {%s}"' % ', '.join(map(lambda('x: \'(%s_id, %s, %s_id)\' % (x[0].name, x[1], x[2].name)'), concrete_policy)), width=100, subsequent_indent=' ' * len('  where "concrete_policy = {'))) ?*/ /*# XXX: fix syntax highlighting: " #*/

lemma policy_from_state: "cdl_state_objs_to_policy CapDLSpec.state = concrete_policy"
  apply (simp add:concrete_policy_def)
  apply (clarsimp simp:cdl_state_objs_to_policy_def)
  apply (rule order_antisym)
   apply (rule subsetI)
   apply (rename_tac edge)
   apply (case_tac edge)
   apply (simp split:split_pair_asm)
   apply (erule cdl_state_bits_to_policy.cases)
    apply (simp add:opt_cap_def slots_of_def opt_object_def CapDLSpec.state_def
              split:split_pair_asm split_case_asm)
    apply (rename_tac subj auth obj ptr cap oref auth' obj_id slot obj')
    /*- for o in obj_space.spec.objs -*/
    apply (case_tac "obj_id = /*? o.name ?*/_id")
      /*- set simps = set(('objects', 'object_slots_def', 'obj_defs')) -*/
      /*- set splits = set() -*/
      /*- if isinstance(o, capdl.TCB) -*/
        /*- do simps.add('%s_caps_def' % o.name) -*/
        /*- do simps.add('cdl_cap_auth_conferred_def') -*/
        /*- do simps.add('vspace_cap_rights_to_auth_def') -*/
        /*- do simps.add('ids') -*/
        /*- do splits.add('split_if_asm') -*/
      /*- endif -*/
      /*? assert(len(simps) > 0) ?*/
     apply (clarsimp simp:/*? ' '.join(simps) ?*/ split:/*? ' '.join(splits) ?*/)
    /*- endfor -*/
  /*? open_proof ?*/clarsimp simp:cdl_state_objs_to_policy_def/*? A ?*/
  /*? a ?*/rule order_antisym; clarsimp/*? A ?*/
   /*? a ?*/rename_tac subject auth object/*? A ?*/
   /*? a ?*/erule cdl_state_bits_to_policy.cases/*? A ?*/
    /*? a ?*/clarsimp/*? A ?*/

    (* subgoal first hack *)
    apply (case_tac "\<not> (case CapDLSpec.objects a of Some (Types_D.CNode _) \<Rightarrow> True | _ \<Rightarrow> False)")
     apply (erule_tac P="case CapDLSpec.objects a of Some (Types_D.CNode _) \<Rightarrow> True | _ \<Rightarrow> False" in notE)
     defer
    apply (subst (asm) not_not)

    /*? a ?*/case_tac cap; frule only_certain_caps, clarsimp/*? A ?*/

         /*# Solve the case for synchronous endpoints. #*/
         /*? a ?*/rename_tac subject b auth object badge rights/*? A ?*/
         /*? a ?*/frule_tac obj=object and badge=badge and rights=rights in which_ep/*? A ?*/
          /*? a ?*/rule refl/*? A ?*/
         /*? a ?*/clarsimp simp:cdl_cap_auth_conferred_def cap_rights_to_auth_def opt_cap_def
                              slots_of_def CapDLSpec.state_def opt_object_def/*? A ?*/

         /*# Figure out if we have any synchronous endpoint caps. If not, the clarsimp above will
          *# have already detected a contradiction in the assumptions and solved the subgoal.
          #*/
         /*- set have_eps = [False] -*/
         /*- for obj in obj_space.spec.objs -*/
           /*- if isinstance(obj, capdl.CNode) -*/
             /*- for cap in obj.slots.values() -*/
               /*- if cap is not none and isinstance(cap.referent, capdl.Endpoint) -*/
                 /*- do have_eps.__setitem__(0, True) -*/
                 /*- break -*/
               /*- endif -*/
             /*- endfor -*/
             /*- if have_eps[0] -*/
               /*- break -*/
             /*- endif -*/
           /*- endif -*/
         /*- endfor -*/

         /*- if have_eps[0] -*/
         /*- for obj in obj_space.spec.objs -*/
         /*? a ?*/case_tac "subject = /*? obj.name ?*/_id"/*? A ?*/
           /*- if obj.is_container() -*/
          /*? a ?*/clarsimp simp:CapDLSpec.objects /*? obj.name ?*/_def object_slots_def /*? obj.name ?*/_caps_def split:split_if_asm/*? A ?*/
           /*- else -*/
          /*? a ?*/clarsimp simp:CapDLSpec.objects /*? obj.name ?*/_def object_slots_def/*? A ?*/
           /*- endif -*/
         /*- endfor -*/
         /*? a ?*/clarsimp simp:CapDLSpec.objects_def empty_irq_objects_def object_slots_def empty_irq_node_def split:split_if_asm/*? A ?*/
         /*- endif -*/
    
        /*# Solve the case for asynchronous endpoints. #*/
        /*? a ?*/rename_tac subject b auth object badge rights/*? A ?*/
        /*? a ?*/frule_tac obj=object and badge=badge and rights=rights in which_aep/*? A ?*/
         /*? a ?*/rule refl/*? A ?*/
        /*? a ?*/clarsimp simp:cdl_cap_auth_conferred_def cap_rights_to_auth_def opt_cap_def
                             slots_of_def CapDLSpec.state_def opt_object_def/*? A ?*/

        /*# Figure out if we have any asynchronous endpoint caps. If not, the clarsimp above will
         *# have already detected a contradiction in the assumptions and solved the subgoal.
         #*/
         /*- set have_aeps = [False] -*/
         /*- for obj in obj_space.spec.objs -*/
           /*- if isinstance(obj, capdl.CNode) -*/
             /*- for cap in obj.slots.values() -*/
               /*- if cap is not none and isinstance(cap.referent, capdl.AsyncEndpoint) -*/
                 /*- do have_aeps.__setitem__(0, True) -*/
                 /*- break -*/
               /*- endif -*/
             /*- endfor -*/
             /*- if have_aeps[0] -*/
               /*- break -*/
             /*- endif -*/
           /*- endif -*/
         /*- endfor -*/

        /*- if have_aeps[0] -*/
        /*- for obj in obj_space.spec.objs -*/
        /*? a ?*/case_tac "subject = /*? obj.name ?*/_id"/*? A ?*/
          /*- if obj.is_container() -*/
         /*? a ?*/clarsimp simp:CapDLSpec.state_def CapDLSpec.cdt_def CapDLSpec.objects /*? obj.name ?*/_def object_slots_def /*? obj.name ?*/_caps_def split:split_if_asm/*? A ?*/
          /*- else -*/
         /*? a ?*/clarsimp simp:CapDLSpec.state_def CapDLSpec.cdt_def CapDLSpec.objects /*? obj.name ?*/_def object_slots_def/*? A ?*/
          /*- endif -*/
        /*- endfor -*/
        /*? a ?*/clarsimp simp:CapDLSpec.objects_def empty_irq_objects_def object_slots_def empty_irq_node_def split:split_if_asm/*? A ?*/
        /*- endif -*/

        (* At this point there are probably a bunch of remaining goals based on other cap types XXX *)

   /*? a ?*/clarsimp simp:CapDLSpec.state_def CapDLSpec.cdt_def/*? A ?*/

/*# Similar loop to the top one, but we track the entire object and cap. #*/
/*- set edges = set() -*/
/*- for obj in obj_space.spec.objs -*/
  /*- if isinstance(obj, capdl.CNode) -*/
    /*- for slot, cap in obj.slots.items() -*/
      /*# The following mimics the logic of `cap_auth_conferred` and `cap_rights_to_auth`. #*/
      /*- if cap is not none -*/
        /*- if isinstance(cap.referent, capdl.Endpoint) -*/
          /*- do edges.add((obj, 'Reset', slot, 'Endpoint', cap)) -*/
          /*- if cap.read -*/
            /*- do edges.add((obj, 'Receive', slot, 'Endpoint', cap)) -*/
          /*- endif -*/
          /*- if cap.write -*/
            /*- do edges.add((obj, 'SyncSend', slot, 'Endpoint', cap)) -*/
          /*- endif -*/
          /*- if cap.grant -*/
            /*- for auth in datatype_auth -*/
              /*- do edges.add((obj, auth, slot, 'Endpoint', cap)) -*/
            /*- endfor -*/
          /*- endif -*/
        /*- elif isinstance(cap.referent, capdl.AsyncEndpoint) -*/
          /*- do edges.add((obj, 'Reset', slot, 'AsyncEndpoint', cap)) -*/
          /*- if cap.read -*/
            /*- do edges.add((obj, 'Receive', slot, 'AsyncEndpoint', cap)) -*/
          /*- endif -*/
          /*- if cap.write -*/
            /*- do edges.add((obj, 'AsyncSyncSend', slot, 'AsyncEndpoint', cap)) -*/
          /*- endif -*/
        /*- else -*/
          /*? raise(TemplateError('unexpected cap type in CNode')) ?*/
        /*- endif -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/

/*# In the logic below, we need to track the statements required to solve the
 *# introduced subgoals, because we are asked to solve them *after* the goal
 *# that benefits from their introduction. Track the steps we need to apply as
 *# a stack in this variable.
 #*/
/*- set finisher = [] -*/
/*- set subgoals = [1] -*/

/*# Now let's use this information to solve the remaining goal. #*/
/*- for edge in edges -*/
  /*- set container = edge[0] -*/
  /*- set auth = edge[1] -*/
  /*- set slot = edge[2] -*/
  /*- set type = edge[3] -*/
  /*- set cap = edge[4] -*/
  /*? ' ' * (subgoals[0] - 1) ?*//*? a ?*/subgoal_tac "(/*? container.name ?*/_id, /*? auth ?*/, /*? cap.referent.name ?*/_id) \<in> cdl_state_bits_to_policy (\<lambda>ref. opt_cap ref CapDLSpec.state) (cdl_cdt CapDLSpec.state)"/*? A ?*/
  /*- do subgoals.__setitem__(0, subgoals[0] + 1) -*/
  /*- do finisher.append('clarsimp simp:opt_cap_def slots_of_def opt_object_def CapDLSpec.state_def CapDLSpec.objects %s_def object_slots_def %s_caps_def cdl_cap_auth_conferred_def cap_rights_to_auth_def' % (container.name, container.name)) -*/
  /*- do finisher.append('(insert cdl_state_bits_to_policy.csbta_caps[where caps="\<lambda>ref. opt_cap ref CapDLSpec.state" and ptr="(%s_id, %s)" and cap="Types_D.%sCap %s_id %s %s%s" and oref=%s_id and auth=%s and cdt="cdl_cdt CapDLSpec.state"])[1]' % (container.name, slot, type, cap.referent.name, cap.badge if cap.badge else 0, 'R' if cap.read else '', 'W' if cap.write else '', cap.referent.name, auth)) -*/
/*- endfor -*/
  /*? ' ' * (subgoals[0] - 1) ?*//*? a ?*/clarsimp/*? A ?*/
  /*- do subgoals.__setitem__(0, subgoals[0] - 1) -*/
/*- for indent in reversed(six.moves.range(subgoals[0])) -*/
  /*? assert(len(finisher) > 1) ?*/
  /*? ' ' * indent ?*//*? a ?*//*? finisher.pop() ?*//*? A ?*/
  /*? ' ' * indent ?*//*? a ?*//*? finisher.pop() ?*//*? close_proof if loop.last else A ?*/
/*- endfor -*/
/*? assert(len(finisher) == 0) ?*/

(** TPP: condense = True *)
lemma state_refines_policy':
  "\<lbrakk>valid_pas pas; (x, auth, y) \<in> cdl_state_objs_to_policy CapDLSpec.state\<rbrakk> \<Longrightarrow>
     (pasObjectAbs pas x, auth, pasObjectAbs pas y) \<in> policy"
  /*? open_proof ?*/rule_tac ?a1.0=x and ?a2.0=auth and ?a3.0=y and s=CapDLSpec.state in cdl_state_objs_to_policy_cases/*? A ?*/
    /*? a ?*/assumption/*? A ?*/
   /*? a ?*/clarsimp simp:cdl_cap_auth_conferred_def/*? A ?*/
   /*? a ?*/case_tac cap; frule only_ep_caps, clarsimp simp:cap_rights_to_auth_def/*? A ?*/

    /*# Solve the subgoal related to authority to synchronous endpoints. #*/
    /*? a ?*/rename_tac ignored badge rights/*? A ?*/
    /*? a ?*/drule_tac obj=y and badge=badge and rights=rights in which_ep/*? A ?*/
     /*? a ?*/rule refl/*? A ?*/
    /*- for obj in obj_space.spec.objs -*/
      /*- if isinstance(obj, capdl.Endpoint) -*/
    /*? a ?*/case_tac "y = /*? obj.name ?*/_id"/*? A ?*/
     /*? a ?*/rule_tac ?a1.0=x and ?a2.0=auth and ?a3.0=/*? obj.name ?*/_id and caps="\<lambda>ref. opt_cap ref CapDLSpec.state" and cdt="cdl_cdt CapDLSpec.state" in cdl_state_bits_to_policy.cases/*? A ?*/
       /*? a ?*/simp add:cdl_state_objs_to_policy_def/*? A ?*/
        /*- for subject, auth, object in concrete_policy -*/
          /*- if id(object) == id(obj) -*/ /*# XXX: if object is obj #*/
      /*? a ?*/case_tac "x = /*? subject.name ?*/_id \<and> auth = /*? auth ?*/"/*? A ?*/
       /*? a ?*/simp add:valid_pas_to_label_of label_of_/*? subject.name ?*/ label_of_/*? object.name ?*/ policy_def/*? A ?*/
          /*- endif -*/
        /*- endfor -*/
      /*? a ?*/simp add:policy_from_state/*? A ?*/
      /*? a ?*/meson/*? A ?*/
     /*? a ?*/simp/*? A ?*/
      /*- endif -*/
    /*- endfor -*/
    /*? a ?*/simp/*? A ?*/

    /*# Solve the subgoal related to authority to asynchronous endpoints. #*/
   /*? a ?*/rename_tac ignored badge rights/*? A ?*/
   /*? a ?*/drule_tac obj=y and badge=badge and rights=rights in which_aep/*? A ?*/
    /*? a ?*/rule refl/*? A ?*/
    /*- for obj in obj_space.spec.objs -*/
      /*- if isinstance(obj, capdl.AsyncEndpoint) -*/
   /*? a ?*/case_tac "y = /*? obj.name ?*/_id"/*? A ?*/
    /*? a ?*/rule_tac ?a1.0=x and ?a2.0=auth and ?a3.0=/*? obj.name ?*/_id and caps="\<lambda>ref. opt_cap ref CapDLSpec.state" and cdt="cdl_cdt CapDLSpec.state" in cdl_state_bits_to_policy.cases/*? A ?*/
      /*? a ?*/simp add:cdl_state_objs_to_policy_def/*? A ?*/
        /*- for subject, auth, object in concrete_policy -*/
          /*- if id(object) == id(obj) -*/ /*# XXX: if object is obj #*/
     /*? a ?*/case_tac "x = /*? subject.name ?*/_id \<and> auth = /*? auth ?*/"/*? A ?*/
      /*? a ?*/simp add:valid_pas_to_label_of label_of_/*? subject.name ?*/ label_of_/*? object.name ?*/ policy_def/*? A ?*/
          /*- endif -*/
        /*- endfor -*/
     /*? a ?*/simp add:policy_from_state/*? A ?*/
     /*? a ?*/meson/*? A ?*/
    /*? a ?*/simp/*? A ?*/
      /*- endif -*/
    /*- endfor -*/
   /*? a ?*/simp/*? A ?*/

    /*# Solve the subgoal related to Control authority. #*/
    /*- for subject, auth, object in concrete_policy -*/
      /*- if auth == 'Control' -*/
  /*? a ?*/case_tac "x = /*? subject.name ?*/_id \<and> y = /*? object.name ?*/_id"/*? A ?*/
   /*? a ?*/simp add:valid_pas_to_label_of label_of_/*? subject.name ?*/ label_of_/*? object.name ?*/ policy_def/*? A ?*/
      /*- endif -*/
    /*- endfor -*/
  /*? a ?*/simp add:policy_from_state/*? close_proof ?*/
(** TPP: condense = False *)

lemma state_refines_policy: "valid_pas pas \<Longrightarrow> pcs_refined pas CapDLSpec.state"
  apply (simp add:pcs_refined_def)
  apply (rule conjI)
   apply (frule irqs_range_pas)
   apply (simp add:valid_pas_def)
   apply (rule allE[OF policy_wf, where x="pasSubject pas"])
   apply assumption
  apply (rule conjI)
   apply (simp add:cdl_irq_map_wellformed_aux_def)
   apply (rule allI)
    apply (simp add:valid_pas_def)
  apply (rule conjI)
   apply (simp add:cdl_tcb_domain_map_wellformed_aux_def)
   defer
  apply (rule conjI)
   apply (clarsimp simp:valid_pas_to_policy auth_graph_map_def)
   apply (rule_tac ?a1.0=x and ?a2.0=auth and ?a3.0=y and s=CapDLSpec.state
                   in cdl_state_objs_to_policy_cases)
     apply assumption
    apply clarsimp
    defer
   apply clarsimp
   apply (subgoal_tac "cdl_cdt CapDLSpec.state = CapDLSpec.cdt")
    prefer 2
    apply (simp add:CapDLSpec.state_def)
   apply (simp add:CapDLSpec.cdt_def)
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac subj auth obj)
   apply (erule cdl_state_asids_to_policy_aux.induct)
     apply (subgoal_tac "cdl_cap_asid' cap = {}")
      prefer 2
      apply (case_tac cap; clarsimp)
          apply ((drule only_ep_caps, simp)+)[5]
     apply simp
    apply ((clarsimp simp:CapDLSpec.state_def CapDLSpec.asid_table_def)+)[2]
  apply (subst valid_pas_to_policy)
   apply assumption
  apply (rule subsetI)
apply (erule cdl_state_irqs_to_policy_aux.induct)
thm subsetI
  apply (rule_tac aag=pas and ?a2.0=Control in cdl_state_irqs_to_policy_aux.cases)
find_theorems  cdl_state_irqs_to_policy_aux
   apply clarsimp


   apply (rule_tac ?a1.0=subj and ?a2.0=auth and ?a3.0=obj and aag=pas and
                   caps="\<lambda>ref. opt_cap ref CapDLSpec.state" and
                   asid_tab="cdl_asid_table CapDLSpec.state" in cdl_state_asids_to_policy_aux.cases)
      apply assumption
     apply clarsimp
     apply (subgoal_tac "cdl_cap_asid' cap = {}")
      prefer 2
      apply (drule no_asids)
      apply (clarsimp)
      apply (case_tac cap; clarsimp)
        apply (tactic \<open>Tactic.distinct_subgoals_tac\<close>)

(*
        valid_pas pas \<Longrightarrow>
       (pasObjectAbs pas a, Control, pasASIDAbs pas (transform_asid_rev (aa, b))) \<in> cdl_state_asids_to_policy pas state \<Longrightarrow> False
*)

      apply (simp add:opt_cap_def slots_of_def opt_object_def)
thm object_slots_def
     apply simp
apply (simp
(\<lambda>ref. opt_cap ref s) (cdl_asid_table s)
   find_theorems  cdl_state_asids_to_policy_aux 



   find_theorems cdl_state_objs_to_policy
find_theorems cdl_cap_auth_conferred
find_theorems auth_graph_map

  oops

/*- endif -*/

end
