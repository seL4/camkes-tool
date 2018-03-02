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

/*# Setup #*/
/*- set thy = me.interface.name -*/

/*- if len(me.parent.from_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single from end are not supported', me.parent)) ?*/
/*- endif -*/
/*- if len(me.parent.to_ends) != 1 -*/
  /*? raise(TemplateError('connections without a single to end are not supported', me.parent)) ?*/
/*- endif -*/

/*- set interface = me.parent.from_interface.type -*/
/*- set have_heap = {8: False, 16: False, 32: False, 64: False} -*/
/*- set used_types = set() -*/
/*- include 'autocorres/have_heap.thy' -*/

/*- macro wrap_facts(indent, xs) -*//*? ('\n%s' % (' ' * indent)).join(textwrap.wrap(' '.join(xs), 100 - indent)) ?*//*- endmacro -*/

(** TPP: condense = True *)
theory "/*? thy ?*/" imports
  /*- if options.verbosity >= 2 -*/
  /*? thy ?*/_base
  /*- else -*/
  "~~/../l4v/tools/autocorres/AutoCorres"
  "~~/../l4v/lib/LemmaBucket"
  "~~/../l4v/lib/WordBitwiseSigned"
  /*- endif -*/
begin
(** TPP: condense = False *)

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

(* FIXME: MOVE *)
lemma circ_break:"\<lbrakk>f = g; h = i\<rbrakk> \<Longrightarrow> f \<circ> h = g \<circ> i"
  by fast

(* FIXME: MOVE *)
lemma update_fn_unwrap:
  "Q = Q' \<Longrightarrow> (\<lambda>a b. if P a b then Q a b else R a b) = (\<lambda>a b. if P a b then Q' a b else R a b)"
  by clarsimp

(* FIXME: MOVE *)
lemma chunk_64[simp]:
  "ucast (
    ((ucast ((scast (x::64 sword))::32 word))::64 word) ||
    (((ucast ((ucast (((scast x)::64 word) >> 32))::32 word))::64 word) << 32)
   ) = x"
  by word_bitwise_signed

(* FIXME: MOVE *)
lemma chunk_s64[simp]:
  "scast (
    ((ucast (x::32 word))::64 sword) || ((ucast (((ucast (y::32 word))::64 word) << 32))::64 sword)) =
    ((ucast x)::64 word) || (((ucast y)::64 word) << 32)"
  by word_bitwise_signed

(* FIXME: MOVE *)
lemma validNF_intro_binder:"\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<Longrightarrow> \<forall>s. \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"
  by simp

/*- set threads = 1 + len(me.parent.to_instance.type.provides + me.parent.to_instance.type.uses + me.parent.to_instance.type.emits + me.parent.to_instance.type.consumes + me.parent.to_instance.type.dataports) -*/

/*- include 'autocorres/debug_abbrevs.thy' -*/

/*- if options.verbosity < 2 -*/
  /*- include 'autocorres/install_code.thy' -*/
/*- endif -*/

(** TPP: condense = True *)
(* Extend the C locale with assumptions on the user's code. *)
locale "/*? thy ?*/_pruned_glue" = "/*? thy ?*/_pruned" +
/*- set user_preconditions = {} -*/
/*- set user_postconditions = {} -*/
/*- set pcount = Counter() -*/
/*- for i, m in enumerate(interface.methods) -*/
  /*- do user_preconditions.__setitem__(m.name, '%s_P' % m.name) -*/
  /*- do user_postconditions.__setitem__(m.name, '%s_Q' % m.name) -*/

  /*# Construct a WP statement that the user must prove. #*/
  /*- set params = [] -*/
  /*- set bound = ['s0'] -*/
  /*- set exist_bound = [] -*/
  /*- set bound_conjs = [] -*/
  /*- set preconditions = ['s = s0', 'inv s'] -*/
  /*- set postconditions = ['inv s'] -*/
  /*- set precondition_type = ['lifted_globals'] -*/
  /*- set postcondition_type = ['lifted_globals', 'lifted_globals'] -*/
  /*- set precondition_params = ['s'] -*/
  /*- set postcondition_params = ['s0', 's'] -*/
  /*- if m.return_type is not none -*/
    /*- do postcondition_params.append('r') -*/
    /*- if m.return_type == 'int8_t' -*/
      /*- do postcondition_type.append('8 sword') -*/
    /*- elif m.return_type in ['char', 'uint8_t'] -*/
      /*- do postcondition_type.append('8 word') -*/
    /*- elif m.return_type == 'int16_t' -*/
      /*- do postcondition_type.append('16 sword') -*/
    /*- elif m.return_type == 'uint16_t' -*/
      /*- do postcondition_type.append('16 word') -*/
    /*- elif m.return_type in ['int', 'int32_t'] -*/
      /*- do postcondition_type.append('32 sword') -*/
    /*- elif m.return_type in ['unsigned int', 'uint32_t'] -*/
      /*- do postcondition_type.append('32 word') -*/
    /*- elif m.return_type == 'int64_t' -*/
      /*- do postcondition_type.append('64 sword') -*/
    /*- elif m.return_type == 'uint64_t' -*/
      /*- do postcondition_type.append('64 word') -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endif -*/
  /*- for p in m.parameters -*/
    /*- set param = 'p%s' % str(pcount) -*/
    /*- do pcount.increment() -*/
    /*- do params.append(param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- set param_type = '8 sword' -*/
      /*- set deref = '%s = ucast (heap_w8 %s (ptr_coerce %s))' -*/
      /*- set ptr_valid = 'ptr_valid_s8 s %s' % param -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- set param_type = '8 word' -*/
      /*- set deref = '%s = heap_w8 %s %s' -*/
      /*- set ptr_valid = 'ptr_valid_u8 s %s' % param -*/
    /*- elif p.type == 'int16_t' -*/
      /*- set param_type = '16 sword' -*/
      /*- set deref = '%s = ucast (heap_w16 %s (ptr_coerce %s))' -*/
      /*- set ptr_valid = 'ptr_valid_s16 s %s' % param -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- set param_type = '16 word' -*/
      /*- set deref = '%s = heap_w16 %s %s' -*/
      /*- set ptr_valid = 'ptr_valid_u16 s %s' % param -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- set param_type = '32 sword' -*/
      /*- set deref = '%s = ucast (heap_w32 %s (ptr_coerce %s))' -*/
      /*- set ptr_valid = 'ptr_valid_s32 s %s' % param -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- set param_type = '32 word' -*/
      /*- set deref = '%s = heap_w32 %s %s' -*/
      /*- set ptr_valid = 'ptr_valid_u32 s %s' % param -*/
    /*- elif p.type == 'int64_t' -*/
      /*- set param_type = '64 sword' -*/
      /*- set deref = '%s = ucast (heap_w64 %s (ptr_coerce %s))' -*/
      /*- set ptr_valid = 'ptr_valid_s64 s %s' % param -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- set param_type = '64 word' -*/
      /*- set deref = '%s = heap_w64 %s %s' -*/
      /*- set ptr_valid = 'ptr_valid_u64 s %s' % param -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
    /*- set disjs = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do disjs.append('%s = Ptr (symbol_table \'\'%s_%s_%d\'\')' % (param, m.name, p.name, t)) -*/
    /*- endfor -*/
    /*- if p.direction == 'in' -*/
      /*- do precondition_type.append(param_type) -*/
      /*- do precondition_params.append(param) -*/
      /*- do postcondition_type.append(param_type) -*/
      /*- do postcondition_params.append(param) -*/
    /*- elif p.direction == 'inout' -*/
      /*- set value_in = '%s_in' % param -*/
      /*- set value_out = '%s_out' % param -*/
      /*- do bound.append(value_in) -*/
      /*- do exist_bound.append(value_out) -*/
      /*- do precondition_type.append(param_type) -*/
      /*- do precondition_params.append(value_in) -*/
      /*- do preconditions.extend([ptr_valid, deref % (value_in, 's', param), '(%s)' % ' \<or> '.join(disjs)]) -*/
      /*- do postcondition_type.extend([param_type, param_type]) -*/
      /*- do postcondition_params.extend([value_in, value_out]) -*/
      /*- do bound_conjs.append(deref % (value_out, 's', param)) -*/
    /*- else -*/
      /*? assert(p.direction == 'out') ?*/
      /*- set value_out = '%s_out' % param -*/
      /*- do exist_bound.append(value_out) -*/
      /*- do preconditions.extend([ptr_valid, '(%s)' % ' \<or> '.join(disjs)]) -*/
      /*- do postcondition_type.append(param_type) -*/
      /*- do postcondition_params.append(value_out) -*/
      /*- do bound_conjs.append(deref % (value_out, 's', param)) -*/
    /*- endif -*/
  /*- endfor -*/
  /*- do precondition_type.append('bool') -*/
  /*- do postcondition_type.append('bool') -*/
  /*- do preconditions.append('%s %s' % (user_preconditions[m.name], ' '.join(precondition_params))) -*/
  /*- do bound_conjs.append('%s %s' % (user_postconditions[m.name], ' '.join(postcondition_params))) -*/
  /*- if len(exist_bound) > 0 -*/
    /*- do postconditions.append('(\<exists>%s. %s)' % (' '.join(exist_bound), ' \<and> '.join(bound_conjs))) -*/
  /*- else -*/
    /*- do postconditions.extend(bound_conjs) -*/
  /*- endif -*/
  fixes /*? user_preconditions[m.name] ?*/ :: "/*? ' \<Rightarrow> '.join(precondition_type) ?*/"
  fixes /*? user_postconditions[m.name] ?*/ :: "/*? ' \<Rightarrow> '.join(postcondition_type) ?*/"
  assumes /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_wp':"\<forall>/*? ' '.join(bound) ?*/. \<lbrace>\<lambda>s. /*? ' \<and> '.join(preconditions) ?*/\<rbrace> /*? me.parent.to_interface.name ?*/_/*? m.name ?*/' /*? ' '.join(params) ?*/ \<lbrace>\<lambda>r s. /*? ' \<and> '.join(postconditions) ?*/\<rbrace>!"

  /*# Assume that setMR is orthogonal to the pre- and post-conditions. #*/
  assumes /*? m.name ?*/_pre_stable_setmr[simp]:"\<And>s i x. /*? user_preconditions[m.name] ?*/ (setMR s i x) = /*? user_preconditions[m.name] ?*/ s"
  assumes /*? m.name ?*/_post_stable_setmr1[simp]:"\<And> s i x. /*? user_postconditions[m.name] ?*/ (setMR s i x) = /*? user_postconditions[m.name] ?*/ s"
  assumes /*? m.name ?*/_post_stable_setmr2[simp]:"\<And> s s' i x. /*? user_postconditions[m.name] ?*/ s (setMR s' i x) = /*? user_postconditions[m.name] ?*/ s s'"

  /*# Assume that updates to the TLS variables are orthogonal to the pre- and
   *# post-conditions.
   #*/
  /*- for p in m.parameters -*/
    /*- if p.type == 'int8_t' -*/
      /*- set update_fn = 'update_s8' -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- set update_fn = 'update_u8' -*/
    /*- elif p.type == 'int16_t' -*/
      /*- set update_fn = 'update_s16' -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- set update_fn = 'update_s16' -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- set update_fn = 'update_s32' -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- set update_fn = 'update_u32' -*/
    /*- elif p.type == 'int64_t' -*/
      /*- set update_fn = 'update_s64' -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- set update_fn = 'update_u64' -*/
    /*- endif -*/
    /*- set disjs = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do disjs.append('p = Ptr (symbol_table \'\'%s_%s_%d\'\')' % (m.name, p.name, t)) -*/
    /*- endfor -*/
  assumes /*? m.name ?*/_pre_stable_update_/*? p.name ?*/[simp]:"\<And>v s p. \<lbrakk>/*? ' \<or> '.join(disjs) ?*/\<rbrakk> \<Longrightarrow> /*? user_preconditions[m.name] ?*/ (/*? update_fn ?*/ s p v) = /*? user_preconditions[m.name] ?*/ s"
  assumes /*? m.name ?*/_post_stable_update_/*? p.name ?*/[simp]:"\<And>v s p. \<lbrakk>/*? ' \<or> '.join(disjs) ?*/\<rbrakk> \<Longrightarrow> /*? user_postconditions[m.name] ?*/ (/*? update_fn ?*/ s p v) = /*? user_postconditions[m.name] ?*/ s"
  /*- endfor -*/

  /*# We need to demand that the user's function leaves all valid pointers
   *# intact for the types of any output arguments because we'll deal with
   *# pointers of these types in _equiv_wp.
   #*/
  /*- set ptr_valids = set() -*/
  /*- set params = ['s', 's\''] -*/
  /*- if m.return_type is not none -*/
    /*- do params.append('r') -*/
  /*- endif -*/
  /*- for i, p in enumerate(m.parameters) -*/
    /*- set param = 'p%d' % i -*/
    /*- if p.direction == 'inout' -*/
      /*- do params.extend(['%s_in' % param, '%s_out' % param]) -*/
    /*- else -*/
      /*- do params.append(param) -*/
    /*- endif -*/
    /*- if p.direction in ['out', 'inout'] -*/
      /*- if p.type == 'int8_t' -*/
        /*- do ptr_valids.add('ptr_valid_s8') -*/
      /*- elif p.type in ['uint8_t', 'char'] -*/
        /*- do ptr_valids.add('ptr_valid_u8') -*/
      /*- elif p.type == 'int16_t' -*/
        /*- do ptr_valids.add('ptr_valid_s16') -*/
      /*- elif p.type == 'uint16_t' -*/
        /*- do ptr_valids.add('ptr_valid_u16') -*/
      /*- elif p.type in ['int32_t', 'int'] -*/
        /*- do ptr_valids.add('ptr_valid_s32') -*/
      /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
        /*- do ptr_valids.add('ptr_valid_u32') -*/
      /*- elif p.type == 'int64_t' -*/
        /*- do ptr_valids.add('ptr_valid_s64') -*/
      /*- elif p.type == 'uint64_t' -*/
        /*- do ptr_valids.add('ptr_valid_u64') -*/
      /*- else -*/
        /*? raise(TemplateError('unsupported')) ?*/
      /*- endif -*/
    /*- endif -*/
  /*- endfor -*/
  /*- for fn in ptr_valids -*/
  assumes /*? fn ?*/_stable_/*? m.name ?*/:"\<And>/*? ' '.join(params) ?*/. /*? user_postconditions[m.name] ?*/ /*? ' '.join(params) ?*/ \<Longrightarrow> /*? fn ?*/ s' = /*? fn ?*/ s"
  /*- endfor -*/

  /*# Assume the globals are in distinct memory. #*/
  /*- for i, p in enumerate(m.parameters) -*/
    /*- for t1 in six.moves.range(1, threads + 1) -*/
      /*- for j, q in enumerate(m.parameters) -*/
        /*- for t2 in six.moves.range(1, threads + 1) -*/
          /*- if i < j or (i == j and t1 < t2) -*/
  assumes /*? m.name ?*/_/*? p.name ?*/_/*? t1 ?*/_/*? m.name ?*/_/*? q.name ?*/_/*? t2 ?*/_distinct[simplified eq_commute, simp]:"symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t1 ?*/'' \<noteq> symbol_table ''/*? m.name ?*/_/*? q.name ?*/_/*? t2 ?*/''"
          /*- endif -*/
        /*- endfor -*/
      /*- endfor -*/
    /*- endfor -*/
  /*- endfor -*/
/*- endfor -*/
begin
(** TPP: condense = False *)

/*- for method_index, m in enumerate(interface.methods) -*/

/*- set input_parameters = list(filter(lambda('x: x.direction in [\'in\', \'inout\']'), m.parameters)) -*/
/*- set output_parameters = list(filter(lambda('x: x.direction in [\'out\', \'inout\']'), m.parameters)) -*/

(** TPP: condense = True *)
/*- set preconditions = ['inv s'] -*/
/*- set postconditions = ['s = s0', 'inv s'] -*/
/*- set setmrs = ['setMR s 0 %d' % method_index] -*/
/*- set params = [] -*/
/*- set packed_payload = [str(method_index)] -*/
/*- set mr = Counter() -*/
/*- do mr.increment() -*/ /*# skip method index #*/
/*- for i, p in enumerate(input_parameters) -*/
  /*- set param = 'p%d' % i -*/
  /*- if p.type in ['int', 'int32_t'] -*/
    /*- do setmrs.__setitem__(0, 'setMR (%s) %s (scast %s)' % (setmrs[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif p.type in ['unsigned int', 'uint32_t'] -*/
    /*- do setmrs.__setitem__(0, 'setMR (%s) %s %s' % (setmrs[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append(param) -*/
  /*- elif p.type in ['char', 'uint8_t', 'uint16_t'] -*/
    /*- do setmrs.__setitem__(0, 'setMR (%s) %s (ucast %s)' % (setmrs[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('ucast %s' % param) -*/
  /*- elif p.type in ['int8_t', 'int16_t'] -*/
    /*- do setmrs.__setitem__(0, 'setMR (%s) %s (scast %s)' % (setmrs[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif p.type == 'uint64_t' -*/
    /*- set lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set upper = str(mr) -*/
    /*- do setmrs.__setitem__(0, 'setMR (setMR (%s) %s (ucast %s)) %s (ucast (%s >> 32))' % (setmrs[0], lower, param, upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['ucast %s' % param, 'ucast (%s >> 32)' % param]) -*/
  /*- elif p.type == 'int64_t' -*/
    /*- set lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set upper = str(mr) -*/
    /*- do setmrs.__setitem__(0, 'setMR (setMR (%s) %s (scast %s)) %s (ucast (((scast %s)::64 word) >> 32))' % (setmrs[0], lower, param, upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['scast %s' % param, 'ucast (((scast %s)::64 word) >> 32)' % param]) -*/
  /*- endif -*/
  /*- do params.append(param) -*/
/*- endfor -*/
/*- do preconditions.append('s0 = %s' % setmrs[0]) -*/
/*- do postconditions.extend(['r = %s' % mr, 'packed s [%s]' % ', '.join(packed_payload)]) -*/
lemma /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_marshal_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s0. \<lbrace>\<lambda>s. /*? ' \<and> '.join(preconditions) ?*/\<rbrace>
          /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_marshal' /*? ' '.join(params) ?*/
        \<lbrace>\<lambda>r s. /*? ' \<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)
  unfolding /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_marshal'_def
  apply (wp seL4_SetMR_wp)
  apply (clarsimp simp:packed_def seL4_MsgMaxLength_def)
  apply (subst getMR_setMR, simp add:seL4_MsgMaxLength_def)+
  apply (simp add:cast_down_s64 cast_down_u64)
  done
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set bound = ['s0'] -*/
/*- set preconditions = ['s = s0', 'inv s'] -*/
/*- set postconditions = ['inv s'] -*/
/*- set unfold_defs = set() -*/ /*# Pointer and heap operations we'll need to unfold #*/
/*- set packed_payload = [str(method_index)] -*/ /*# The contents of the IPC buffer. #*/
/*- set effect = ['s0'] -*/ /*# The effect on the state of running this function. #*/
/*- set distincts = {} -*/ /*# Requirements for no pointer aliasing. #*/
/*- set update_equivs = set() -*/ /*# heap_w*_update_equivs rules we may need to apply. #*/
/*- for i, p in enumerate(input_parameters) -*/
  /*- set param = 'p%d' % i -*/
  /*- if p.type in ['int', 'int32_t'] -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_s32 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_s32 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s32 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_s32_def', 'ptr_contains_s32_def', 'update_s32_def'))) -*/
    /*- if 32 not in distincts -*/
      /*- do distincts.__setitem__(32, []) -*/
    /*- endif -*/
    /*- do distincts[32].append('((ptr_coerce %s)::32 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w32_update_equiv') -*/
  /*- elif p.type in ['unsigned int', 'uint32_t'] -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_u32 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_u32 s %s %s' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u32 (%s) %s %s' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_u32_def', 'ptr_contains_u32_def', 'update_u32_def'))) -*/
    /*- if 32 not in distincts -*/
      /*- do distincts.__setitem__(32, []) -*/
    /*- endif -*/
    /*- do distincts[32].append('((ptr_coerce %s)::32 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w32_update_equiv') -*/
  /*- elif p.type == 'uint16_t' -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_u16 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_u16 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u16 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_u16_def', 'ptr_contains_u16_def', 'update_u16_def'))) -*/
    /*- if 16 not in distincts -*/
      /*- do distincts.__setitem__(16, []) -*/
    /*- endif -*/
    /*- do distincts[16].append('((ptr_coerce %s)::16 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w16_update_equiv') -*/
  /*- elif p.type == 'int16_t' -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_s16 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_s16 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s16 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_s16_def', 'ptr_contains_s16_def', 'update_s16_def'))) -*/
    /*- if 16 not in distincts -*/
      /*- do distincts.__setitem__(16, []) -*/
    /*- endif -*/
    /*- do distincts[16].append('((ptr_coerce %s)::16 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w16_update_equiv') -*/
  /*- elif p.type in ['char', 'uint8_t'] -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_u8 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_u8 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u8 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_u8_def', 'ptr_contains_u8_def', 'update_u8_def'))) -*/
    /*- if 8 not in distincts -*/
      /*- do distincts.__setitem__(8, []) -*/
    /*- endif -*/
    /*- do distincts[8].append('((ptr_coerce %s)::8 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w8_update_equiv') -*/
  /*- elif p.type == 'int8_t' -*/
    /*- set packed_value = 'p%d\'' % i -*/
    /*- do preconditions.append('ptr_valid_s8 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_s8 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s8 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_s8_def', 'ptr_contains_s8_def', 'update_s8_def'))) -*/
    /*- if 8 not in distincts -*/
      /*- do distincts.__setitem__(8, []) -*/
    /*- endif -*/
    /*- do distincts[8].append('((ptr_coerce %s)::8 word ptr)' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do update_equivs.add('heap_w8_update_equiv') -*/
  /*- elif p.type == 'uint64_t' -*/
    /*- set packed_lower = 'p%d\'_lower' % i -*/
    /*- set packed_upper = 'p%d\'_upper' % i -*/
    /*- do preconditions.append('ptr_valid_u64 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_u64 s %s ((ucast %s) || ((ucast %s) << 32))' % (param, packed_lower, packed_upper)) -*/
    /*- do effect.__setitem__(0, 'update_u64 (%s) %s ((ucast %s) || ((ucast %s) << 32))' % (effect[0], param, packed_lower, packed_upper)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_u64_def', 'ptr_contains_u64_def', 'update_u64_def'))) -*/
    /*- if 64 not in distincts -*/
      /*- do distincts.__setitem__(64, []) -*/
    /*- endif -*/
    /*- do distincts[64].append('((ptr_coerce %s)::64 word ptr)' % param) -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do update_equivs.add('heap_w64_update_equiv') -*/
  /*- elif p.type == 'int64_t' -*/
    /*- set packed_lower = 'p%d\'_lower' % i -*/
    /*- set packed_upper = 'p%d\'_upper' % i -*/
    /*- do preconditions.append('ptr_valid_s64 s %s' % param) -*/
    /*- do postconditions.append('ptr_contains_s64 s %s (ucast (((ucast %s)::64 word) || (((ucast %s)::64 word) << 32)))' % (param, packed_lower, packed_upper)) -*/
    /*- do effect.__setitem__(0, 'update_s64 (%s) %s (ucast (((ucast %s)::64 word) || (((ucast %s)::64 word) << 32)))' % (effect[0], param, packed_lower, packed_upper)) -*/
    /*- do list(map(unfold_defs.add, ('ptr_valid_s64_def', 'ptr_contains_s64_def', 'update_s64_def'))) -*/
    /*- if 64 not in distincts -*/
      /*- do distincts.__setitem__(64, []) -*/
    /*- endif -*/
    /*- do distincts[64].append('((ptr_coerce %s)::64 word ptr)' % param) -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do update_equivs.add('heap_w64_update_equiv') -*/
  /*- endif -*/
/*- endfor -*/
/*- for k, v in distincts.items() -*/
  /*# Requiring distinct pointers is only relevant when we have more than one pointer of this type. #*/
  /*- if len(v) > 1 -*/
    /*- do preconditions.append('distinct [%s]' % ', '.join(v)) -*/
  /*- endif -*/
/*- endfor -*/
/*- do bound.extend(packed_payload[1:]) -*/
/*- do preconditions.append('packed s [%s]' % ', '.join(packed_payload)) -*/
/*- do postconditions.append('s = %s' % effect[0]) -*/
/*# Lemmas chain to apply after proof completion. #*/
/*- set postprocessing = len(packed_payload[1:]) * ['THEN all_pair_unwrap[THEN iffD2]'] + ['THEN validNF_make_schematic_post', 'simplified'] -*/
lemma /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_unmarshal_wp[/*? ', '.join(postprocessing) ?*/]:
  "\<forall>/*? ' '.join(bound) ?*/. \<lbrace>\<lambda>s. /*? ' \<and> '.join(preconditions) ?*/\<rbrace>
          /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_unmarshal' /*? ' '.join(params) ?*/
        \<lbrace>\<lambda>_ s. /*? ' \<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)+
  unfolding /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_unmarshal'_def
  apply (wp seL4_GetMR_wp)
  apply (clarsimp simp:seL4_MsgMaxLength_def /*? ' '.join(unfold_defs) ?*/)
  apply (clarsimp simp:getmr_packed ucast_id)
  /*# The simplifier reorders multiple heap accesses, so we structure this step
   *# such that we don't care which heap operation is outermost. #*/
  apply (((rule /*? '|rule '.join(update_equivs) ?*/), rule ext, rule ext, simp add:getmr_packed ucast_id)+)?
  apply simp
  done
(** TPP: condense = False *)

(** TPP: condense = True *)
lemma /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_invoke_subst:
  "/*? me.parent.to_interface.name ?*/_/*? m.name ?*/_invoke' = /*? me.parent.to_interface.name ?*/_/*? m.name ?*/'"
  by (clarsimp simp:/*? me.parent.to_interface.name ?*/_/*? m.name ?*/_invoke'_def /*? me.parent.to_interface.name ?*/_/*? m.name ?*/'_def intro!:ext)
(** TPP: condense = False *)

/*- set postprocessing = [] -*/
/*- for p in m.parameters -*/
  /*- if p.direction == 'inout' -*/
    /*- do postprocessing.append('THEN all_pair_unwrap[THEN iffD2]') -*/
  /*- endif -*/
/*- endfor -*/
/*- do postprocessing.extend(['THEN validNF_make_schematic_post', 'simplified']) -*/
lemmas /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_wp = /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_wp'[/*? ', '.join(postprocessing) ?*/]

(** TPP: condense = True *)
/*- set params = [] -*/
/*- set postconditions = [] -*/
/*- set effect = ['s0'] -*/
/*- set mr = Counter() -*/
/*- set packed_payload = [] -*/
/*- if m.return_type is not none -*/
  /*- set param = 'ret' -*/
  /*- do params.append(param) -*/
  /*- if m.return_type in ['int', 'int32_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (scast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif m.return_type in ['unsigned int', 'uint32_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s %s' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append(param) -*/
  /*- elif m.return_type in ['char', 'uint8_t', 'uint16_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (ucast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('ucast %s' % param) -*/
  /*- elif m.return_type in ['int8_t', 'int16_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (scast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif m.return_type == 'uint64_t' -*/
    /*- set mr_lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set mr_upper = str(mr) -*/
    /*- do effect.__setitem__(0, 'setMR (setMR (%s) %s (ucast %s)) %s (ucast (%s >> 32))' % (effect[0], mr_lower, param, mr_upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['ucast %s' % param, 'ucast (%s >> 32)' % param]) -*/
  /*- elif m.return_type == 'int64_t' -*/
    /*- set mr_lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set mr_upper = str(mr) -*/
    /*- do effect.__setitem__(0, 'setMR (setMR (%s) %s (scast %s)) %s (ucast (((scast %s)::64 word) >> 32))' % (effect[0], mr_lower, param, mr_upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['scast %s' % param, 'ucast (((scast %s)::64 word) >> 32)' % param]) -*/
  /*- endif -*/
/*- endif -*/
/*- for i, p in enumerate(output_parameters) -*/
  /*- set param = 'p%d' % i -*/
  /*- do params.append(param) -*/
  /*- if p.type in ['int', 'int32_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (scast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif p.type in ['unsigned int', 'uint32_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s %s' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append(param) -*/
  /*- elif p.type in ['char', 'uint8_t', 'uint16_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (ucast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('ucast %s' % param) -*/
  /*- elif p.type in ['int8_t', 'int16_t'] -*/
    /*- do effect.__setitem__(0, 'setMR (%s) %s (scast %s)' % (effect[0], mr, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.append('scast %s' % param) -*/
  /*- elif p.type == 'uint64_t' -*/
    /*- set mr_lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set mr_upper = str(mr) -*/
    /*- do effect.__setitem__(0, 'setMR (setMR (%s) %s (ucast %s)) %s (ucast (%s >> 32))' % (effect[0], mr_lower, param, mr_upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['ucast %s' % param, 'ucast (%s >> 32)' % param]) -*/
  /*- elif p.type == 'int64_t' -*/
    /*- set mr_lower = str(mr) -*/
    /*- do mr.increment() -*/
    /*- set mr_upper = str(mr) -*/
    /*- do effect.__setitem__(0, 'setMR (setMR (%s) %s (scast %s)) %s (ucast (((scast %s)::64 word) >> 32))' % (effect[0], mr_lower, param, mr_upper, param)) -*/
    /*- do mr.increment() -*/
    /*- do packed_payload.extend(['scast %s' % param, 'ucast (((scast %s)::64 word) >> 32)' % param]) -*/
  /*- endif -*/
/*- endfor -*/
/*- do postconditions.extend(['r = %s' % mr, 's = %s' % effect[0], 'packed s [%s]' % ', '.join(packed_payload)]) -*/
lemma /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_marshal_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s0. \<lbrace>\<lambda>s. s = s0 \<and> inv s\<rbrace>
          /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_marshal' /*? ' '.join(params) ?*/
        \<lbrace>\<lambda>r s. /*? ' \\<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)
  unfolding /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_marshal'_def
  apply (wp seL4_SetMR_wp)
  apply (clarsimp simp:packed_def seL4_MsgMaxLength_def getMR_setMR)
  done
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set preconditions = ['s = s0', 'inv s'] -*/
/*- set postconditions = ['inv s'] -*/
/*- set pre_packed = [str(method_index)] -*/
/*- set bound = ['s0'] -*/
/*- set precondition_params = ['s'] -*/
/*- set postprocessing = ['THEN validNF_make_schematic_post', 'simplified'] -*/
/*- set exist_bound = [] -*/
/*- set postcondition_params = ['s0', 's'] -*/
/*- set post_packed = [] -*/
/*- if m.return_type is not none -*/
  /*- set param = 'ru' -*/
  /*- do exist_bound.append(param) -*/
  /*- do postcondition_params.append(param) -*/
  /*- if m.return_type == 'int8_t' -*/
    /*- do post_packed.append('scast %s' % param) -*/
  /*- elif m.return_type in ['uint8_t', 'char'] -*/
    /*- do post_packed.append('ucast %s' % param) -*/
  /*- elif m.return_type == 'int16_t' -*/
    /*- do post_packed.append('scast %s' % param) -*/
  /*- elif m.return_type == 'uint16_t' -*/
    /*- do post_packed.append('ucast %s' % param) -*/
  /*- elif m.return_type in ['int32_t', 'int'] -*/
    /*- do post_packed.append('scast %s' % param) -*/
  /*- elif m.return_type in ['uint32_t', 'unsigned int'] -*/
    /*- do post_packed.append(param) -*/
  /*- elif m.return_type == 'int64_t' -*/
    /*- do post_packed.append('scast %s' % param) -*/
    /*- do post_packed.append('ucast (((scast %s)::64 word) >> 32)' % param) -*/
  /*- elif m.return_type == 'uint64_t' -*/
    /*- do post_packed.append('ucast %s' % param) -*/
    /*- do post_packed.append('ucast (%s >> 32)' % param) -*/
  /*- else -*/
    /*? raise(TemplateError('unsupported')) ?*/
  /*- endif -*/
/*- endif -*/
/*- for i, p in enumerate(m.parameters) -*/
  /*- set param = 'p%d' % i -*/
  /*- do postcondition_params.append(param) -*/
  /*- if p.direction == 'in' -*/
    /*- do bound.append(param) -*/
    /*- do postprocessing.insert(0, 'THEN all_pair_unwrap[THEN iffD2]') -*/
    /*- do precondition_params.append(param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do pre_packed.append('scast %s' % param) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do pre_packed.append(param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
      /*- do pre_packed.append('ucast (((scast %s)::64 word) >> 32)' % param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
      /*- do pre_packed.append('ucast (%s >> 32)' % param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- elif p.direction == 'inout' -*/
    /*- do bound.append(param) -*/
    /*- do precondition_params.append(param) -*/
    /*- do postprocessing.insert(0, 'THEN all_pair_unwrap[THEN iffD2]') -*/
    /*- do exist_bound.append('%s_out' % param) -*/
    /*- do postcondition_params.append('%s_out' % param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
      /*- do post_packed.append('scast %s_out' % param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
      /*- do post_packed.append('ucast %s_out' % param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
      /*- do post_packed.append('scast %s_out' % param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
      /*- do post_packed.append('ucast %s_out' % param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do pre_packed.append('scast %s' % param) -*/
      /*- do post_packed.append('scast %s_out' % param) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do pre_packed.append(param) -*/
      /*- do post_packed.append('%s_out' % param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do pre_packed.append('scast %s' % param) -*/
      /*- do pre_packed.append('ucast (((scast %s)::64 word) >> 32)' % param) -*/
      /*- do post_packed.append('scast %s_out' % param) -*/
      /*- do post_packed.append('ucast (((scast %s_out)::64 word) >> 32)' % param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do pre_packed.append('ucast %s' % param) -*/
      /*- do pre_packed.append('ucast (%s >> 32)' % param) -*/
      /*- do post_packed.append('ucast %s_out' % param) -*/
      /*- do post_packed.append('ucast (%s_out >> 32)' % param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- else -*/
    /*? assert(p.direction == 'out') ?*/
    /*- do exist_bound.append(param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- do post_packed.append('scast %s' % param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do post_packed.append('ucast %s' % param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do post_packed.append('scast %s' % param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do post_packed.append('ucast %s' % param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do post_packed.append('scast %s' % param) -*/
    /*- elif p.type in ['uint16_t', 'unsigned int'] -*/
      /*- do post_packed.append('%s' % param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do post_packed.append('scast %s' % param) -*/
      /*- do post_packed.append('ucast (((scast %s)::64 word) >> 32)' % param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do post_packed.append('ucast %s' % param) -*/
      /*- do post_packed.append('ucast (%s >> 32)' % param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endif -*/
/*- endfor -*/

/*- do preconditions.append('packed s [%s]' % ', '.join(pre_packed)) -*/
/*- do preconditions.append('%s %s' % (user_preconditions[m.name], ' '.join(precondition_params))) -*/

/*- if len(exist_bound) > 0 -*/
  /*- do postconditions.append('(\<exists>%s. packed s [%s] \<and> %s %s)' % (' '.join(exist_bound), ', '.join(post_packed), user_postconditions[m.name], ' '.join(postcondition_params))) -*/
/*- else -*/
  /*- do postconditions.append('packed s [%s]' % ', '.join(post_packed)) -*/
  /*- do postconditions.append('%s %s' % (user_postconditions[m.name], ' '.join(postcondition_params))) -*/
/*- endif -*/
lemma /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_internal_wp[/*? ', '.join(postprocessing) ?*/]:
  "\<forall>/*? ' '.join(bound) ?*/. \<lbrace>\<lambda>s. /*? ' \<and> '.join(preconditions) ?*/\<rbrace>
          /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_internal'
        \<lbrace>\<lambda>r s. /*? ' \<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)+
  unfolding /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_internal'_def
  apply (subst /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_invoke_subst)
  /*- set wps = ['%s_%s_unmarshal_wp' % (me.parent.to_interface.name, m.name), '%s_%s_wp' % (me.parent.to_interface.name, m.name), '%s_%s_marshal_wp' % (me.parent.to_interface.name, m.name)] -*/
  /*- for p in m.parameters -*/
    /*- do wps.append('get_%s_%s_wp' % (m.name, p.name)) -*/
  /*- endfor -*/
  apply (wp /*? wrap_facts(len('  apply (wp '), wps) ?*/)
  apply clarsimp

  (* HACK: around Isabelle sucking the outermost conjoined implication into the assumptions. *)
  /*- if len(m.parameters) >= 2 -*/
    /*- set disjs = [] -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do disjs.append('rv = Ptr (symbol_table \'\'%s_%s_%d\'\')' % (m.name, m.parameters[0].name, t)) -*/
    /*- endfor -*/
    /*- for p in m.parameters[1:] -*/
      /*- for t in six.moves.range(1, threads + 1) -*/
  apply (subgoal_tac "/*? ' \<or> '.join(disjs) ?*/ \<longrightarrow> ((ptr_coerce rv)::32 word ptr) \<noteq> Ptr (symbol_table ''/*? m.name ?*/_/*? p.name ?*/_/*? t ?*/'')")
   prefer 2
   apply fastforce
      /*- endfor -*/
    /*- endfor -*/
  /*# We should now have sufficient bits in our assumptions to direct the
   *# simplifier's careless rampage.
   #*/
  apply clarsimp
  /*- endif -*/

  /*# Try and get rid of some ptr_valid stuff. #*/
  /*- set rules = set() -*/
  /*- for p in m.parameters -*/
    /*- do rules.add('inv_imp_%s_%s_valid' % (m.name, p.name)) -*/
    /*- for t in six.moves.range(1, threads + 1) -*/
      /*- do rules.add('inv_imp_%s_%s_%d_valid' % (m.name, p.name, t)) -*/
    /*- endfor -*/
    /*- if p.type == 'int8_t' -*/
      /*- do rules.add('ptr_valid_s8_def') -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do rules.add('ptr_valid_u8_def') -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do rules.add('ptr_valid_s16_def') -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do rules.add('ptr_valid_u16_def') -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do rules.add('ptr_valid_s32_def') -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do rules.add('ptr_valid_u32_def') -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do rules.add('ptr_valid_s64_def') -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do rules.add('ptr_valid_u64_def') -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endfor -*/
  apply (clarsimp simp:/*? wrap_facts(len('  apply (clarsimp simp:'), rules) ?*/)

  /*# From here on, significant dynamism starts creeping into this proof and
   *# you should prefix all steps with the expansion of ' ' * (subgoals[0] - 1)
   *# to ensure you get the right indentation in the generated output.
   #*/
  /*- set subgoals = [1] -*/

  /*- if len(m.parameters) > 0 -*/
    /*# At this point we've got one major subgoal left and a bunch of trivial
     *# subgoals we ourselves have introduced that we can dispatch later with
     *# fastforce. The major subgoal is a bit of a tricky bastard and has a set
     *# of nested conjoined implications. We need to unravel it in order to apply
     *# exI so we do that by tracking the depth (nested \<longrightarrow>s) and
     *# width (conjuncts) of the remaining interesting subgoals.
     #*/
    /*- set goals = [{'width':threads, 'depth':len(m.parameters) - 1}] -*/

    /*# For each pending goal there is some ambiguity about which TLS variables
     *# are backing each parameter. As we conjI our way through this we
     *# explore the different possibilities. When we finally bottom out in a
     *# concrete case we need to know how to instantiate existentially bound
     *# variables to the TLS variables we've chosen in this path. To do this,
     *# we track a 'possible' set of backing variables for each parameter. If
     *# we've got this right all these sets should be singletons when we bottom
     *# out. We initialise these sets here.
     #*/
    /*- do goals[0].__setitem__('params', []) -*/
    /*- for i, p in enumerate(m.parameters) -*/
      /*- do goals[0]['params'].append([]) -*/
      /*- for t in six.moves.range(1, threads + 1) -*/
        /*- do goals[0]['params'][i].append('%s_%s_%d' % (m.name, p.name, t)) -*/
      /*- endfor -*/
    /*- endfor -*/

    /*# We also want to track which parameter has caused the conjunct we're
     *# currently chopping up. Note that the 'width' setting can be derived as:
     *#  len(goal['params'][goal['active']])
     *# We track it separately because the currently active variable is invalid
     *# when we bottom out of the case distinction.
     #*/
    /*- do goals[0].__setitem__('active', 1) -*/

    /*# We'll consume these as we bottom out in the case distinction. #*/
    /*- set instantiations = [] -*/
    /*- for p in m.parameters -*/
      /*- if p.direction == 'out' -*/
        /*- for t in six.moves.range(1, threads + 1) -*/
          /*- do instantiations.append('Ptr (symbol_table \'\'%s_%s_%d\'\')' % (m.name, p.name, t)) -*/
        /*- endfor -*/
      /*- endif -*/
    /*- endfor -*/

    /*- for _ in six.moves.range(10000) -*/ /*# XXX: ~infinite loop #*/
      /*- if len(goals) == 0 -*/
        /*- break -*/
      /*- endif -*/
      /*- set goal = goals.pop() -*/
      /*- if goal['depth'] == 0 -*/

        /*# At this point we've bottomed out in something that requires
         *# explicit instantiation of the packed parameters. There's
         *# potentially some leading conjuncts though, that talk about some
         *# awkward distinctness of casted 64-bit pointers.
        #*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply ((rule conjI, clarsimp)+)?
  /*? ' ' * (subgoals[0] - 1) ?*/(* Instantiate the contents of the IPC buffer. *)
        /*- for i, p in enumerate(m.parameters) -*/
          /*- set param = 'p%d' % i -*/
          /*- if p.direction in ['in', 'inout'] -*/
            /*- if p.type == 'int8_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast /*? param ?*/" in exI)
            /*- elif p.type in ['uint8_t', 'char'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast /*? param ?*/" in exI)
            /*- elif p.type == 'int16_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast /*? param ?*/" in exI)
            /*- elif p.type == 'uint16_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast /*? param ?*/" in exI)
            /*- elif p.type in ['int32_t', 'int'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast /*? param ?*/" in exI)
            /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x=/*? param ?*/ in exI)
            /*- elif p.type == 'int64_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast /*? param ?*/" in exI)
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast (((scast /*? param ?*/)::64 word) >> 32)" in exI)
            /*- elif p.type == 'uint64_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast /*? param ?*/" in exI)
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast (/*? param ?*/ >> 32)" in exI)
            /*- else -*/
              /*? raise(TemplateError('unsupported')) ?*/
            /*- endif -*/
          /*- endif -*/
        /*- endfor -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply clarsimp

        /*# If there are inout parameters, they will be existentially bound in
         *# the precondition we're looking at now.
         #*/
        /*- set shown_comment = [False] -*/
        /*- for i, p in enumerate(m.parameters) -*/
          /*- if p.direction == 'inout' -*/
            /*- if not shown_comment[0] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/(* Instantiate inout parameters. *)
              /*- do shown_comment.__setitem__(0, True) -*/
            /*- endif -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x=p/*? i ?*/ in exI)
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule conjI)
            /*- do subgoals.__setitem__(0, subgoals[0] + 1) -*/
            /*- set extra_simps = set() -*/
            /*- if p.type == 'int8_t' -*/
              /*- set in_heap = 'heap_w8' -*/
              /*- do extra_simps.add('heap_w8_update_s8') -*/
            /*- elif p.type in ['uint8_t', 'char'] -*/
              /*- set in_heap = 'heap_w8' -*/
              /*- do extra_simps.add('heap_w8_update_u8') -*/
            /*- elif p.type == 'int16_t' -*/
              /*- set in_heap = 'heap_w16' -*/
              /*- do extra_simps.add('heap_w16_update_s16') -*/
            /*- elif p.type == 'uint16_t' -*/
              /*- set in_heap = 'heap_w16' -*/
              /*- do extra_simps.add('heap_w16_update_u16') -*/
            /*- elif p.type in ['int', 'int32_t'] -*/
              /*- set in_heap = 'heap_w32' -*/
              /*- do extra_simps.add('heap_w32_update_s32') -*/
            /*- elif p.type in ['unsigned int', 'uint32_t'] -*/
              /*- set in_heap = 'heap_w32' -*/
              /*- do extra_simps.add('heap_w32_update_u32') -*/
            /*- elif p.type == 'int64_t' -*/
              /*- set in_heap = 'heap_w64' -*/
              /*- do extra_simps.add('heap_w64_update_s64') -*/
            /*- elif p.type == 'uint64_t' -*/
              /*- set in_heap = 'heap_w64' -*/
              /*- do extra_simps.add('heap_w64_update_u64') -*/
            /*- else -*/
              /*? raise(TemplateError('unsupported')) ?*/
            /*- endif -*/
            /*- for q in m.parameters -*/
              /*- if q.type == 'int8_t' -*/
                /*- do extra_simps.add('%s_update_s8' % in_heap) -*/
              /*- elif q.type in ['uint8_t', 'char'] -*/
                /*- do extra_simps.add('%s_update_u8' % in_heap) -*/
              /*- elif q.type == 'int16_t' -*/
                /*- do extra_simps.add('%s_update_s16' % in_heap) -*/
              /*- elif q.type == 'uint16_t' -*/
                /*- do extra_simps.add('%s_update_u16' % in_heap) -*/
              /*- elif q.type in ['int', 'int32_t'] -*/
                /*- do extra_simps.add('%s_update_s32' % in_heap) -*/
              /*- elif q.type in ['unsigned int', 'uint32_t'] -*/
                /*- do extra_simps.add('%s_update_u32' % in_heap) -*/
              /*- elif q.type == 'int64_t' -*/
                /*- do extra_simps.add('%s_update_s64' % in_heap) -*/
              /*- elif q.type == 'uint64_t' -*/
                /*- do extra_simps.add('%s_update_u64' % in_heap) -*/
              /*- else -*/
                /*? raise(TemplateError('unsupported')) ?*/
              /*- endif -*/
            /*- endfor -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (clarsimp simp:/*? ' '.join(extra_simps) ?*/)
            /*- do subgoals.__setitem__(0, subgoals[0] - 1) -*/
          /*- endif -*/
        /*- endfor -*/

        /*# We'll need this information in a moment. #*/
        /*- set ptr_contains = set() -*/
        /*- for p in m.parameters -*/
          /*- if p.type == 'int8_t' -*/
            /*- do ptr_contains.add('ptr_contains_s8_def') -*/
          /*- elif p.type in ['uint8_t', 'char'] -*/
            /*- do ptr_contains.add('ptr_contains_u8_def') -*/
          /*- elif p.type == 'int16_t' -*/
            /*- do ptr_contains.add('ptr_contains_s16_def') -*/
          /*- elif p.type == 'uint16_t' -*/
            /*- do ptr_contains.add('ptr_contains_u16_def') -*/
          /*- elif p.type in ['int32_t', 'int'] -*/
            /*- do ptr_contains.add('ptr_contains_s32_def') -*/
          /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
            /*- do ptr_contains.add('ptr_contains_u32_def') -*/
          /*- elif p.type == 'int64_t' -*/
            /*- do ptr_contains.add('ptr_contains_s64_def') -*/
          /*- elif p.type == 'uint64_t' -*/
            /*- do ptr_contains.add('ptr_contains_u64_def') -*/
          /*- else -*/
            /*? raise(TemplateError('unsupported')) ?*/
          /*- endif -*/
        /*- endfor -*/

  /*? ' ' * (subgoals[0] - 1) ?*/(* Peel off and solve the user's precondition. *)
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule conjI)
        /*- do subgoals.__setitem__(0, subgoals[0] + 1) -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (clarsimp simp:/*? ' '.join(ptr_contains) ?*/, fastforce?)[1]
        /*- do subgoals.__setitem__(0, subgoals[0] - 1) -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply clarsimp

  /*? ' ' * (subgoals[0] - 1) ?*/(* Instantiate the (post) contents of the IPC buffer. *)
        /*- if m.return_type is not none -*/
          /*- if m.return_type == 'int8_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast rva" in exI) /*# FIXME: something more stable than rva here. #*/
          /*- elif m.return_type in ['uint8_t', 'char'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast rva" in exI)
          /*- elif m.return_type == 'int16_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast rva" in exI)
          /*- elif m.return_type == 'uint16_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast rva" in exI)
          /*- elif m.return_type in ['int32_t', 'int'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast rva" in exI)
          /*- elif m.return_type in ['uint32_t', 'unsigned int'] -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x=rva in exI)
          /*- elif m.return_type == 'int64_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="scast rva" in exI)
          /*- elif m.return_type == 'uint64_t' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="ucast rva" in exI)
          /*- else -*/
            /*? raise(TemplateError('unsupported')) ?*/
          /*- endif -*/
        /*- endif -*/
        /*- for i, p in enumerate(m.parameters) -*/
          /*# As we're in this 'leaf' branch, we should know precisely what TLS
           *# variable backs every parameter. Note that the first parameter is,
           *# as discussed above, annoyingly sucked into the premises and thus
           *# we still don't know exactly what it is.
           #*/
          /*? assert(i == 0 or len(goal['params'][i]) == 1) ?*/
          /*- set param = goal['params'][i][0] -*/
          /*- if p.direction in ['inout', 'out'] -*/
            /*- if p.type == 'int8_t' -*/
              /*- set deref = 'ucast (heap_w8 s\' (ptr_coerce %s))' -*/
            /*- elif p.type in ['uint8_t', 'char'] -*/
              /*- set deref = 'heap_w8 s\' %s' -*/
            /*- elif p.type == 'int16_t' -*/
              /*- set deref = 'ucast (heap_w16 s\' (ptr_coerce %s))' -*/
            /*- elif p.type == 'uint16_t' -*/
              /*- set deref = 'heap_w16 s\' %s' -*/
            /*- elif p.type in ['int32_t', 'int'] -*/
              /*- set deref = 'ucast (heap_w32 s\' (ptr_coerce %s))' -*/
            /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
              /*- set deref = 'heap_w32 s\' %s' -*/
            /*- elif p.type == 'int64_t' -*/
              /*- set deref = 'ucast (heap_w64 s\' (ptr_coerce %s))' -*/
            /*- elif p.type == 'uint64_t' -*/
              /*- set deref = 'heap_w64 s\' %s' -*/
            /*- else -*/
              /*? raise(TemplateError('unsupported')) ?*/
            /*- endif -*/
            /*- if i == 0 and p.direction == 'inout' -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="/*? deref % 'rv' ?*/" in exI)
            /*- else -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule_tac x="/*? deref % '(Ptr (symbol_table \'\'%s\'\'))' % param ?*/" in exI)
            /*- endif -*/
          /*- endif -*/
        /*- endfor -*/

  /*? ' ' * (subgoals[0] - 1) ?*/(* Finally, knock off the postcondition. *)
  /*? ' ' * (subgoals[0] - 1) ?*/apply (clarsimp simp:/*? ' '.join(ptr_contains) ?*/)
        /*- do subgoals.__setitem__(0, subgoals[0] - 1) -*/

      /*- elif goal['width'] > 1 -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply (rule conjI)
        /*- do subgoals.__setitem__(0, subgoals[0] + 1) -*/
        /*? assert(len(goal['params'][goal['active']]) == goal['width']) ?*/
        /*- set extracted_goal = copy.deepcopy(goal) -*/
        /*- do extracted_goal.__setitem__('width', 1) -*/
        /*- do extracted_goal['params'].__setitem__(extracted_goal['active'], [extracted_goal['params'][extracted_goal['active']][0]]) -*/
        /*- do goal.__setitem__('width', goal['width'] - 1) -*/
        /*- do goal['params'].__setitem__(goal['active'], goal['params'][goal['active']][1:]) -*/
        /*- do goals.extend([goal, extracted_goal]) -*/

      /*- else -*/
  /*? ' ' * (subgoals[0] - 1) ?*/apply clarsimp
        /*- do goal.__setitem__('width', threads) -*/
        /*- do goal.__setitem__('depth', goal['depth'] - 1) -*/
        /*- do goal.__setitem__('active', goal['active'] + 1) -*/
        /*- do goals.append(goal) -*/

      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/

  done
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set bound = ['s0'] -*/
/*- set preconditions = ['s = s0', 'inv s'] -*/
/*- set postconditions = ['inv s'] -*/
/*- set effect = ['s0'] -*/
/*- set packed_payload = [] -*/
/*- set distincts = {} -*/
/*- set unfold_defs = set() -*/
/*- if m.return_type is not none -*/
  /*- set packed_value = 'ret' -*/
  /*- if m.return_type in ['char', 'uint8_t', 'int8_t', 'uint16_t', 'int16_t'] -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('r = ucast %s' % packed_value) -*/
  /*- elif m.return_type in ['unsigned int', 'uint32_t'] -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('r = %s' % packed_value) -*/
  /*- elif m.return_type in ['int', 'int32_t'] -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('r = ucast %s' % packed_value) -*/
  /*- elif m.return_type == 'uint64_t' -*/
    /*- set packed_lower = '%s_lower' % packed_value -*/
    /*- set packed_upper = '%s_upper' % packed_value -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do postconditions.append('r = ((ucast %s) || ((ucast %s) << 32))' % (packed_lower, packed_upper)) -*/
  /*- elif m.return_type == 'int64_t' -*/
    /*- set packed_lower = '%s_lower' % packed_value -*/
    /*- set packed_upper = '%s_upper' % packed_value -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do postconditions.append('r = ucast (((ucast %s)::64 word) || (((ucast %s)::64 word) << 32))' % (packed_lower, packed_upper)) -*/
  /*- endif -*/
/*- endif -*/
/*- set params = [] -*/
/*- for i, p in enumerate(output_parameters) -*/
  /*- set param = 'p%d' % i -*/
  /*- set packed_value = '%s\'' % param -*/
  /*- if p.type in ['char', 'uint8_t'] -*/
    /*- do preconditions.append('ptr_valid_u8 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_u8 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u8 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- if 8 not in distincts -*/
      /*- do distincts.__setitem__(8, []) -*/
    /*- endif -*/
    /*- do distincts[8].append('((ptr_coerce %s)::8 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_u8_def', 'update_u8_def', 'ptr_valid_u8_def'))) -*/
  /*- elif p.type == 'int8_t' -*/
    /*- do preconditions.append('ptr_valid_s8 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_s8 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s8 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- if 8 not in distincts -*/
      /*- do distincts.__setitem__(8, []) -*/
    /*- endif -*/
    /*- do distincts[8].append('((ptr_coerce %s)::8 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_s8_def', 'update_s8_def', 'ptr_valid_s8_def'))) -*/
  /*- elif p.type == 'uint16_t' -*/
    /*- do preconditions.append('ptr_valid_u16 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_u16 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u16 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- if 16 not in distincts -*/
      /*- do distincts.__setitem__(16, []) -*/
    /*- endif -*/
    /*- do distincts[16].append('((ptr_coerce %s)::16 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_u16_def', 'update_u16_def', 'ptr_valid_u16_def'))) -*/
  /*- elif p.type == 'int16_t' -*/
    /*- do preconditions.append('ptr_valid_s16 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_s16 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s16 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- if 16 not in distincts -*/
      /*- do distincts.__setitem__(16, []) -*/
    /*- endif -*/
    /*- do distincts[16].append('((ptr_coerce %s)::16 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_s16_def', 'update_s16_def', 'ptr_valid_s16_def'))) -*/
  /*- elif p.type in ['unsigned int', 'uint32_t'] -*/
    /*- do preconditions.append('ptr_valid_u32 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_u32 s %s %s' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_u32 (%s) %s %s' % (effect[0], param, packed_value)) -*/
    /*- if 32 not in distincts -*/
      /*- do distincts.__setitem__(32, []) -*/
    /*- endif -*/
    /*- do distincts[32].append('((ptr_coerce %s)::32 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_u32_def', 'update_u32_def', 'ptr_valid_u32_def'))) -*/
  /*- elif p.type in ['int', 'int32_t'] -*/
    /*- do preconditions.append('ptr_valid_s32 s %s' % param) -*/
    /*- do packed_payload.append(packed_value) -*/
    /*- do postconditions.append('ptr_contains_s32 s %s (ucast %s)' % (param, packed_value)) -*/
    /*- do effect.__setitem__(0, 'update_s32 (%s) %s (ucast %s)' % (effect[0], param, packed_value)) -*/
    /*- if 32 not in distincts -*/
      /*- do distincts.__setitem__(32, []) -*/
    /*- endif -*/
    /*- do distincts[32].append('((ptr_coerce %s)::32 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_s32_def', 'update_s32_def', 'ptr_valid_s32_def'))) -*/
  /*- elif p.type == 'uint64_t' -*/
    /*- set packed_lower = '%s_lower' % packed_value -*/
    /*- set packed_upper = '%s_upper' % packed_value -*/
    /*- do preconditions.append('ptr_valid_u64 s %s' % param) -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do postconditions.append('ptr_contains_u64 s %s ((ucast %s) || ((ucast %s) << 32))' % (param, packed_lower, packed_upper)) -*/
    /*- do effect.__setitem__(0, 'update_u64 (%s) %s ((ucast %s) || ((ucast %s) << 32))' % (effect[0], param, packed_lower, packed_upper)) -*/
    /*- if 64 not in distincts -*/
      /*- do distincts.__setitem__(64, []) -*/
    /*- endif -*/
    /*- do distincts[64].append('((ptr_coerce %s)::64 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_u64_def', 'update_u64_def', 'ptr_valid_u64_def'))) -*/
  /*- elif p.type == 'int64_t' -*/
    /*- set packed_lower = '%s_lower' % packed_value -*/
    /*- set packed_upper = '%s_upper' % packed_value -*/
    /*- do preconditions.append('ptr_valid_s64 s %s' % param) -*/
    /*- do packed_payload.extend([packed_lower, packed_upper]) -*/
    /*- do postconditions.append('ptr_contains_s64 s %s (ucast (((ucast %s)::64 word) || (((ucast %s)::64 word) << 32)))' % (param, packed_lower, packed_upper)) -*/
    /*- do effect.__setitem__(0, 'update_s64 (%s) %s (ucast (((ucast %s)::64 word) || (((ucast %s)::64 word) << 32)))' % (effect[0], param, packed_lower, packed_upper)) -*/
    /*- if 64 not in distincts -*/
      /*- do distincts.__setitem__(64, []) -*/
    /*- endif -*/
    /*- do distincts[64].append('((ptr_coerce %s)::64 word ptr)' % param) -*/
    /*- do list(map(unfold_defs.add, ('ptr_contains_s64_def', 'update_s64_def', 'ptr_valid_s64_def'))) -*/
  /*- endif -*/
  /*- do params.append(param) -*/
/*- endfor -*/
/*- for k, v in distincts.items() -*/
  /*# Requiring distinct pointers is only relevant when we have more than one pointer of this type. #*/
  /*- if len(v) > 1 -*/
    /*- do preconditions.append('distinct [%s]' % ', '.join(v)) -*/
  /*- endif -*/
/*- endfor -*/
/*- do bound.extend(packed_payload) -*/
/*- do preconditions.append('packed s [%s]' % ', '.join(packed_payload)) -*/
/*- do postconditions.append('s = %s' % effect[0]) -*/
/*# Lemmas chain to apply after proof completion. #*/
/*- set postprocessing = len(packed_payload) * ['THEN all_pair_unwrap[THEN iffD2]'] + ['THEN validNF_make_schematic_post', 'simplified'] -*/
lemma /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_unmarshal_wp[/*? ', '.join(postprocessing) ?*/]:
  "\<forall>/*? ' '.join(bound) ?*/. \<lbrace>\<lambda>s. /*? ' \\<and> '.join(preconditions) ?*/\<rbrace>
          /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_unmarshal' /*? ' '.join(params) ?*/
        \<lbrace>\<lambda>r s. /*? ' \\<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)+
  unfolding /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_unmarshal'_def
  apply (wp seL4_GetMR_wp)
  apply (clarsimp simp:packed_def seL4_MsgMaxLength_def ucast_id /*? ' '.join(unfold_defs) ?*/)
  /*# XXX: Really quite upsetting that the simplifier needs an assist here to
   *# solve `2 = Suc (Suc 0)`.
   #*/
  apply (simp add:numeral_2_eq_2 cong del:if_weak_cong)?
  done
(** TPP: condense = False *)

(** TPP: condense = True *)
/*- set preconditions = ['s = s0', 'inv s'] -*/
/*- set postconditions = ['inv s'] -*/

/*- set precondition_params = ['s'] -*/
/*- set marshal_params = [] -*/
/*- set unmarshal_params = [] -*/
/*- set postcondition_params = ['s0', 's'] -*/

/*- if m.return_type is not none -*/
  /*- do postcondition_params.append('r') -*/
/*- endif -*/

/*- set ptr_distincts = {} -*/

/*- for i, p in enumerate(m.parameters) -*/
  /*- set param = 'p%d' % i -*/

  /*- if p.direction == 'in' -*/
    /*- do precondition_params.append(param) -*/
    /*- do marshal_params.append(param) -*/
    /*- do postcondition_params.append(param) -*/

  /*- elif p.direction == 'inout' -*/
    /*- do precondition_params.append(param) -*/
    /*- do marshal_params.append(param) -*/
    /*- do postcondition_params.append(param) -*/
    /*- do unmarshal_params.append('%s_out' % param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w8 s (ptr_coerce %s_out)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s8 s %s_out' % param) -*/
      /*- if 8 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(8, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[8].append('%s_out' % param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do postcondition_params.append('(heap_w8 s %s_out)' % param) -*/
      /*- do preconditions.append('ptr_valid_u8 s %s_out' % param) -*/
      /*- if 8 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(8, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[8].append('%s_out' % param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w16 s (ptr_coerce %s_out)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s16 s %s_out' % param) -*/
      /*- if 16 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(16, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[16].append('%s_out' % param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do postcondition_params.append('(heap_w16 s %s_out)' % param) -*/
      /*- do preconditions.append('ptr_valid_u16 s %s_out' % param) -*/
      /*- if 16 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(16, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[16].append('%s_out' % param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do postcondition_params.append('(ucast (heap_w32 s (ptr_coerce %s_out)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s32 s %s_out' % param) -*/
      /*- if 32 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(32, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[32].append('%s_out' % param) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do postcondition_params.append('(heap_w32 s %s_out)' % param) -*/
      /*- do preconditions.append('ptr_valid_u32 s %s_out' % param) -*/
      /*- if 32 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(32, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[32].append('%s_out' % param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w64 s (ptr_coerce %s_out)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s64 s %s_out' % param) -*/
      /*- if 64 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(64, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[64].append('%s_out' % param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do postcondition_params.append('(heap_w64 s %s_out)' % param) -*/
      /*- do preconditions.append('ptr_valid_u64 s %s_out' % param) -*/
      /*- if 64 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(64, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[64].append('%s_out' % param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/

  /*- else -*/
    /*? assert(p.direction == 'out') ?*/
    /*- do unmarshal_params.append(param) -*/
    /*- if p.type == 'int8_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w8 s (ptr_coerce %s)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s8 s %s' % param) -*/
      /*- if 8 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(8, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[8].append(param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do postcondition_params.append('(heap_w8 s %s)' % param) -*/
      /*- do preconditions.append('ptr_valid_u8 s %s' % param) -*/
      /*- if 8 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(8, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[8].append(param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w16 s (ptr_coerce %s)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s16 s %s' % param) -*/
      /*- if 16 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(16, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[16].append(param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do postcondition_params.append('(heap_w16 s %s)' % param) -*/
      /*- do preconditions.append('ptr_valid_u16 s %s' % param) -*/
      /*- if 16 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(16, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[16].append(param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do postcondition_params.append('(ucast (heap_w32 s (ptr_coerce %s)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s32 s %s' % param) -*/
      /*- if 32 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(32, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[32].append(param) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do postcondition_params.append('(heap_w32 s %s)' % param) -*/
      /*- do preconditions.append('ptr_valid_u32 s %s' % param) -*/
      /*- if 32 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(32, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[32].append(param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do postcondition_params.append('(ucast (heap_w64 s (ptr_coerce %s)))' % param) -*/
      /*- do preconditions.append('ptr_valid_s64 s %s' % param) -*/
      /*- if 64 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(64, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[64].append(param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do postcondition_params.append('(heap_w64 s %s)' % param) -*/
      /*- do preconditions.append('ptr_valid_u64 s %s' % param) -*/
      /*- if 64 not in ptr_distincts -*/
        /*- do ptr_distincts.__setitem__(64, []) -*/
      /*- endif -*/
      /*- do ptr_distincts[64].append(param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/

  /*- endif -*/
/*- endfor -*/

/*# Require that the user pointers we're marshalling the result into are all
 *# distinct.
 #*/
/*- for k, v in ptr_distincts.items() -*/
  /*- if len(v) > 1 -*/
    /*# not as bad as it looks #*/
    /*- do preconditions.append('distinct [%s]' % ', '.join(map(lambda('x: \'((ptr_coerce %%s)::%d word ptr)\' %% x' % k), v))) -*/
  /*- endif -*/
/*- endfor -*/

/*- set orthogonal_updates = [] -*/
/*- for i, p in enumerate(m.parameters) -*/
  /*- if p.direction in ['inout', 'out'] -*/
    /*- if p.direction == 'inout' -*/
      /*- set param = 'p%d_out' % i -*/
    /*- else -*/
      /*- set param = 'p%d' % i -*/
    /*- endif -*/
    /*- if p.type == 'int8_t' -*/
      /*- do orthogonal_updates.append('update_s8 s2 %s' % param) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do orthogonal_updates.append('update_u8 s2 %s' % param) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do orthogonal_updates.append('update_s16 s2 %s' % param) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do orthogonal_updates.append('update_u16 s2 %s' % param) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do orthogonal_updates.append('update_s32 s2 %s' % param) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do orthogonal_updates.append('update_u32 s2 %s' % param) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do orthogonal_updates.append('update_s64 s2 %s' % param) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do orthogonal_updates.append('update_u64 s2 %s' % param) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endif -*/
/*- endfor -*/
/*- for upd in orthogonal_updates -*/
  /*- do preconditions.append('(\<forall>s1 s2 v. %s s1 (%s v) = %s s1 s2)' % (user_postconditions[m.name], upd, user_postconditions[m.name])) -*/
/*- endfor -*/

/*- do preconditions.append('%s %s' % (user_preconditions[m.name], ' '.join(precondition_params))) -*/
/*- do postconditions.append('%s %s' % (user_postconditions[m.name], ' '.join(postcondition_params))) -*/

lemma /*? me.parent.from_interface.name ?*/_/*? me.parent.to_interface.name ?*/_/*? m.name ?*/_equiv_wp:
  "\<forall>s0. \<lbrace>\<lambda>s. /*? ' \<and> '.join(preconditions) ?*/\<rbrace>
          do /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_marshal' /*? ' '.join(marshal_params) ?*/;
             /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_internal';
             /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_unmarshal' /*? ' '.join(unmarshal_params) ?*/
          od
        \<lbrace>\<lambda>r s. /*? ' \<and> '.join(postconditions) ?*/\<rbrace>!"
  apply (rule allI)+
  apply (wp /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_unmarshal_wp
            /*? me.parent.to_interface.name ?*/_/*? m.name ?*/_internal_wp
            /*? me.parent.from_interface.name ?*/_/*? m.name ?*/_marshal_wp)
  apply clarsimp
  /*- for i, p in enumerate(m.parameters) -*/
    /*- if p.direction in ['in', 'inout'] -*/
  apply (rule_tac x=p/*? i ?*/ in exI)
    /*- endif -*/
  /*- endfor -*/

  /*- set ptr_valids = set() -*/
  /*- for p in output_parameters -*/
    /*- if p.type == 'int8_t' -*/
      /*- do ptr_valids.add('ptr_valid_s8_stable_%s' % m.name) -*/
    /*- elif p.type in ['uint8_t', 'char'] -*/
      /*- do ptr_valids.add('ptr_valid_u8_stable_%s' % m.name) -*/
    /*- elif p.type == 'int16_t' -*/
      /*- do ptr_valids.add('ptr_valid_s16_stable_%s' % m.name) -*/
    /*- elif p.type == 'uint16_t' -*/
      /*- do ptr_valids.add('ptr_valid_u16_stable_%s' % m.name) -*/
    /*- elif p.type in ['int32_t', 'int'] -*/
      /*- do ptr_valids.add('ptr_valid_s32_stable_%s' % m.name) -*/
    /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
      /*- do ptr_valids.add('ptr_valid_u32_stable_%s' % m.name) -*/
    /*- elif p.type == 'int64_t' -*/
      /*- do ptr_valids.add('ptr_valid_s64_stable_%s' % m.name) -*/
    /*- elif p.type == 'uint64_t' -*/
      /*- do ptr_valids.add('ptr_valid_u64_stable_%s' % m.name) -*/
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endfor -*/
  /*- if len(input_parameters) > 0 or len(ptr_valids) > 0 -*/
    /*- if len(ptr_valids) > 0 -*/
  apply (clarsimp simp:/*? ' '.join(ptr_valids) ?*/)
    /*- else -*/
  apply clarsimp
    /*- endif -*/
  /*- endif -*/

  /*- if m.return_type is not none -*/
    /*- if m.return_type == 'int8_t' -*/
  apply (rule_tac x="scast ru" in exI)
    /*- elif m.return_type in ['uint8_t', 'char'] -*/
  apply (rule_tac x="ucast ru" in exI)
    /*- elif m.return_type == 'int16_t' -*/
  apply (rule_tac x="scast ru" in exI)
    /*- elif m.return_type == 'uint16_t' -*/
  apply (rule_tac x="ucast ru" in exI)
    /*- elif m.return_type in ['int32_t', 'int'] -*/
  apply (rule_tac x="scast ru" in exI)
    /*- elif m.return_type in ['uint32_t', 'unsigned int'] -*/
  apply (rule_tac x=ru in exI)
    /*- elif m.return_type == 'int64_t' -*/
  apply (rule_tac x="scast ru" in exI)
  apply (rule_tac x="ucast (((scast ru)::64 word) >> 32)" in exI)
    /*- elif m.return_type == 'uint64_t' -*/
  apply (rule_tac x="ucast ru" in exI)
  apply (rule_tac x="ucast (ru >> 32)" in exI)
    /*- else -*/
      /*? raise(TemplateError('unsupported')) ?*/
    /*- endif -*/
  /*- endif -*/

  /*- set heap_update_fns = set() -*/
  /*- for i, p in enumerate(m.parameters) -*/
    /*- if p.direction in ['inout', 'out'] -*/
      /*- if p.direction == 'inout' -*/
        /*- set param = 'p%d_outa' % i -*/
      /*- else -*/
        /*? assert(p.direction == 'out') ?*/
        /*- set param = 'p%da' % i -*/
      /*- endif -*/
      /*- if p.type == 'int8_t' -*/
  apply (rule_tac x="scast /*? param ?*/" in exI)
        /*- do heap_update_fns.add('heap_w8_update_s8') -*/
      /*- elif p.type in ['uint8_t', 'char'] -*/
  apply (rule_tac x="ucast /*? param ?*/" in exI)
        /*- do heap_update_fns.add('heap_w8_update_u8') -*/
      /*- elif p.type == 'int16_t' -*/
  apply (rule_tac x="scast /*? param ?*/" in exI)
        /*- do heap_update_fns.add('heap_w16_update_s16') -*/
      /*- elif p.type == 'uint16_t' -*/
  apply (rule_tac x="ucast /*? param ?*/" in exI)
        /*- do heap_update_fns.add('heap_w16_update_u16') -*/
      /*- elif p.type in ['int32_t', 'int'] -*/
  apply (rule_tac x="scast /*? param ?*/" in exI)
        /*- do heap_update_fns.add('heap_w32_update_s32') -*/
      /*- elif p.type in ['uint32_t', 'unsigned int'] -*/
  apply (rule_tac x=/*? param ?*/ in exI)
        /*- do heap_update_fns.add('heap_w32_update_u32') -*/
      /*- elif p.type == 'int64_t' -*/
  apply (rule_tac x="scast /*? param ?*/" in exI)
  apply (rule_tac x="ucast (((scast /*? param ?*/)::64 word) >> 32)" in exI)
        /*- do heap_update_fns.add('heap_w64_update_s64') -*/
      /*- elif p.type == 'uint64_t' -*/
  apply (rule_tac x="ucast /*? param ?*/" in exI)
  apply (rule_tac x="ucast (/*? param ?*/ >> 32)" in exI)
        /*- do heap_update_fns.add('heap_w64_update_u64') -*/
      /*- else -*/
        /*? raise(TemplateError('unsupported')) ?*/
      /*- endif -*/
    /*- endif -*/
  /*- endfor -*/

  /*- if m.return_type is not none or len(output_parameters) > 0 -*/
    /*- if len(heap_update_fns) > 0 -*/
  apply (clarsimp simp:/*? ' '.join(heap_update_fns) ?*/)
    /*- else -*/
  apply clarsimp
    /*- endif -*/
  /*- endif -*/

  /*# For some reason that's not clear to me, signed 64-bit return types cause
   *# part of the goal not to be solved by clarsimp alone.
   #*/
  /*- if m.return_type == 'int64_t' -*/
  apply (metis chunk_64 ucast_scast_id)
  /*- endif -*/

  done
(** TPP: condense = False *)

/*- endfor -*/

end

end
