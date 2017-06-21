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

/*- if 'autocorres/ptr.thy' not in included -*/
/*- do included.add('autocorres/ptr.thy') -*/

/*- include 'autocorres/getmr_setmr.thy' -*/

/*- macro ptr_valid_t(lemmas, size, signed) -*/
  /*- set name = 'ptr_valid_%s%d' % ('s' if signed else 'u', size) -*/
  /*- if '%s_def' % name not in lemmas -*/
    /*- set word = '%sword' % ('s' if signed else '') -*/
definition
  /*? name ?*/ :: "lifted_globals \<Rightarrow> /*? size ?*/ /*? word ?*/ ptr \<Rightarrow> bool"
where
  "/*? name ?*/ s p \<equiv> is_valid_w/*? size ?*/ s /*- if signed -*/(ptr_coerce /*- endif -*/p/*- if signed -*/)/*- endif -*/"
    /*- do lemmas.add('%s_def' % name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro ptr_contains_t(lemmas, size, signed) -*/
  /*- set name = 'ptr_contains_%s%d' % ('s' if signed else 'u', size) -*/
  /*- if '%s_def' % name not in lemmas -*/
    /*- set word = '%sword' % ('s' if signed else '') -*/
definition
  /*? name ?*/ :: "lifted_globals \<Rightarrow> /*? size ?*/ /*? word ?*/ ptr \<Rightarrow> /*? size ?*/ /*? word ?*/ \<Rightarrow> bool"
where
  "/*? name ?*/ s p v \<equiv> ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ s p \<and> heap_w/*? size ?*/ s /*- if signed -*/(ptr_coerce /*- endif -*/p/*- if signed -*/)/*- endif -*/ = /*- if signed -*/scast /*- endif -*/v"
    /*- do lemmas.add('%s_def' % name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro ptr_contains_t_valid(lemmas, size, signed) -*/
  /*- set name = 'ptr_contains_%s%d_valid' % ('s' if signed else 'u', size) -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:
  "ptr_contains_/*? 's' if signed else 'u' ?*//*? size ?*/ s p v \<Longrightarrow> ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ s p"
  by (clarsimp simp:ptr_contains_/*? 's' if signed else 'u' ?*//*? size ?*/_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro ptr_contains_t_setmr(lemmas, size, signed) -*/
  /*- set name = 'ptr_contains_%s%d_setmr' % ('s' if signed else 'u', size) -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:"ptr_contains_/*? 's' if signed else 'u' ?*//*? size ?*/ (setMR s i x) p v = ptr_contains_/*? 's' if signed else 'u' ?*//*? size ?*/ s p v"
  by (clarsimp simp:ptr_contains_/*? 's' if signed else 'u' ?*//*? size ?*/_def ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/_def setMR_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro ptr_valid_t_setmr(lemmas, size, signed) -*/
  /*- set name = 'ptr_valid_%s%d_setmr' % ('s' if signed else 'u', size) -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:"ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ (setMR s i x) p = ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ s p"
  by (clarsimp simp:ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/_def setMR_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- set ptr_lemmas = set() -*/

/*- for m in interface.methods -*/
/*- for p in m.parameters -*/

/*- if p.type in ['int', 'int32_t'] -*/
  /*? ptr_valid_t(ptr_lemmas, 32, True) ?*/
  /*? ptr_contains_t(ptr_lemmas, 32, True) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 32, True) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 32, True) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 32, True) ?*/

/*- elif p.type in ['unsigned int', 'uint32_t'] -*/
  /*? ptr_valid_t(ptr_lemmas, 32, False) ?*/
  /*? ptr_contains_t(ptr_lemmas, 32, False) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 32, False) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 32, False) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 32, False) ?*/

/*- elif p.type == 'int8_t' -*/
  /*? ptr_valid_t(ptr_lemmas, 8, True) ?*/
  /*? ptr_contains_t(ptr_lemmas, 8, True) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 8, True) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 8, True) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 8, True) ?*/

/*- elif p.type in ['char', 'uint8_t'] -*/
  /*? ptr_valid_t(ptr_lemmas, 8, False) ?*/
  /*? ptr_contains_t(ptr_lemmas, 8, False) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 8, False) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 8, False) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 8, False) ?*/

/*- elif p.type == 'uint64_t' -*/
  /*? ptr_valid_t(ptr_lemmas, 64, False) ?*/
  /*? ptr_contains_t(ptr_lemmas, 64, False) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 64, False) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 64, False) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 64, False) ?*/

/*- elif p.type == 'int64_t' -*/
  /*? ptr_valid_t(ptr_lemmas, 64, True) ?*/
  /*? ptr_contains_t(ptr_lemmas, 64, True) ?*/
  /*? ptr_contains_t_valid(ptr_lemmas, 64, True) ?*/
  /*? ptr_contains_t_setmr(ptr_lemmas, 64, True) ?*/
  /*? ptr_valid_t_setmr(ptr_lemmas, 64, True) ?*/

/*- endif -*/

/*- endfor -*/
/*- endfor -*/

/*- endif -*/
