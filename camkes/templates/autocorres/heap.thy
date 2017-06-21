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

/*- if 'autocorres/heap.thy' not in included -*/
/*- do included.add('autocorres/heap.thy') -*/

/*# If we're working with the heap -- which we almost certainly are if our
 *# interfaces are non-trivial -- we'd like some helpers to express operations
 *# on the heap. However, we can't unconditionally declare all of these
 *# because, e.g., if none of our interfaces use 'char' parameters, we will not
 *# have a w8 heap. The logic below declares one copy of each of the defs and
 *# lemmas that are relevant to our current scenario.
 #*/

/*- include 'autocorres/inv.thy' -*/
/*- include 'autocorres/getmr_setmr.thy' -*/

/*- macro update_t_def(lemmas, size, signed) -*/
  /*- set name = 'update_%s%d' % ('s' if signed else 'u', size) -*/
  /*- if '%s_def' % name not in lemmas -*/
    /*- set word = '%sword' % ('s' if signed else '') -*/
definition
  /*? name ?*/ :: "lifted_globals \<Rightarrow> /*? size ?*/ /*? word ?*/ ptr \<Rightarrow> /*? size ?*/ /*? word ?*/ \<Rightarrow> lifted_globals"
where
  "/*? name ?*/ s p v \<equiv> heap_w/*? size ?*/_update (\<lambda>f q. if q = /*- if signed -*/ptr_coerce /*- endif -*/p then /*- if signed -*/scast /*- endif -*/v else f q) s"
    /*- do lemmas.add('%s_def' % name) -*/
  /*- endif -*/

  /*- set fn = 'update_%s%d' % ('s' if signed else 'u', size) -*/
  /*- set name = 'setmr_%s_reorder' % fn -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:"setMR (/*? fn ?*/ s p v) i x = /*? fn ?*/ (setMR s i x) p v"
  by (simp add:setMR_def /*? fn ?*/_def ipc_buffer_def ipc_buffer_ptr_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro heap_t_update_preserves_inv(lemmas, size) -*/
  /*- set name = 'heap_w%d_update_preserves_inv' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:
  "inv s \<Longrightarrow> inv (heap_w/*? size ?*/_update f s)"
  by (simp add:inv_defs)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro heap_t_update_equiv(lemmas, size) -*/
  /*- set name = 'heap_w%d_update_equiv' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/:
  "\<lbrakk>f = g; s = s'\<rbrakk> \<Longrightarrow> heap_w/*? size ?*/_update f s = heap_w/*? size ?*/_update g s'"
  by clarsimp
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro heap_t_update_compose(lemmas, size, signed) -*/
  /*- set name = 'heap_w%d_update_compose' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/:
  "heap_w/*? size ?*/_update (f \<circ> g) s = heap_w/*? size ?*/_update f (heap_w/*? size ?*/_update g s)"
  by clarsimp
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro getmr_heap_t_update(lemmas, size) -*/
  /*- set name = 'getmr_heap_w%d_update' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:
  "getMR (heap_w/*? size ?*/_update f s) i = getMR s i"
  by (simp add:getMR_def ipc_buffer_def ipc_buffer_ptr_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro setmr_heap_t_update_reorder(lemmas, size) -*/
  /*- set name = 'setmr_heap_w%d_update_reorder' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/:
  "setMR (heap_w/*? size ?*/_update f s) i x = heap_w/*? size ?*/_update f (setMR s i x)"
  by (simp add:setMR_def ipc_buffer_def ipc_buffer_ptr_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro cast_ucast_id_t(lemmas, size, signed) -*/
  /*- set name = '%scast_ucast_id_%s%d' % ('s' if signed else 'u', 's' if signed else 'u', size) -*/
  /*- if name not in lemmas -*/
    /*- set word = '%sword' % ('s' if signed else '') -*/
lemma /*? name ?*/[simp]:
  "((/*? 's' if signed else 'u' ?*/cast ((ucast (x::/*? size ?*/ /*? word ?*/))::32 word))::/*? size ?*/ /*? word ?*/) = x"
  by (simp add:ucast_id)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro heap_update_preserves_ptr_valid_t(lemmas, size, signed) -*/
  /*- set name = 'heap_w%d_update_preserves_ptr_valid_%s%d' % (size, 's' if signed else 'u', size) -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]:
  "ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ s p \<Longrightarrow> ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/ (heap_w/*? size ?*/_update f s) p"
  by (simp add:ptr_valid_/*? 's' if signed else 'u' ?*//*? size ?*/_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro of_int_via_ucast_t(lemmas, size) -*/
  /*- set name = 'of_int_via_ucast_%d' % size -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]: "((ucast ((of_int x)::/*? size ?*/ word))::/*? size ?*/ sword) = of_int x"
  by simp
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro update_t_preserves_inv(lemmas, size, signed) -*/
  /*- set fn = 'update_%s%d' % ('s' if signed else 'u', size) -*/
  /*- set name = '%s_preserves_inv' % fn -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]: "inv s \<Longrightarrow> inv (/*? fn ?*/ s p v)"
  by (simp add:/*? fn ?*/_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- macro is_valid_update_t(lemmas, size, signed, valid_size) -*/
  /*- set is_valid_fn = 'is_valid_w%d' % valid_size -*/
  /*- set update_fn = 'update_%s%d' % ('s' if signed else 'u', size) -*/
  /*- set name = '%s_%s' % (is_valid_fn, update_fn) -*/
  /*- if name not in lemmas -*/
lemma /*? name ?*/[simp]: "/*? is_valid_fn ?*/ (/*? update_fn ?*/ s p v) = /*? is_valid_fn ?*/ s"
  by (simp add:/*? update_fn ?*/_def)
    /*- do lemmas.add(name) -*/
  /*- endif -*/
/*- endmacro -*/

/*- set heap_lemmas = set() -*/

/*- for m in interface.methods -*/
/*- for p in m.parameters -*/

/*- if p.type in ['int', 'int32_t'] -*/
  /*# Lemmas and defs for signed 32-bit heap. #*/
  /*? update_t_def(heap_lemmas, 32, True) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 32) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 32) ?*/
  /*? heap_t_update_compose(heap_lemmas, 32) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 32) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 32) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 32, True) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 32) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 32, True) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, True, 8) ?*/
  /*- endif -*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, True, 16) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 32, True, 32) ?*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, True, 64) ?*/
  /*- endif -*/

/*- elif p.type in ['unsigned int', 'uint32_t'] -*/
  /*# Lemmas and defs for unsigned 32-bit heap. #*/
  /*? update_t_def(heap_lemmas, 32, False) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 32) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 32) ?*/
  /*? heap_t_update_compose(heap_lemmas, 32) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 32) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 32) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 32, False) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 32) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 32, False) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, False, 8) ?*/
  /*- endif -*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, False, 16) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 32, False, 32) ?*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 32, False, 64) ?*/
  /*- endif -*/

/*- elif p.type == 'int8_t' -*/
  /*# Lemmas and defs for signed 8-bit heap. #*/
  /*? update_t_def(heap_lemmas, 8, True) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 8) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 8) ?*/
  /*? heap_t_update_compose(heap_lemmas, 8) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 8) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 8) ?*/
  /*? cast_ucast_id_t(heap_lemmas, 8, True) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 8, True) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 8) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 8, True) ?*/
  /*? is_valid_update_t(heap_lemmas, 8, True, 8) ?*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, True, 16) ?*/
  /*- endif -*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, True, 32) ?*/
  /*- endif -*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, True, 64) ?*/
  /*- endif -*/

/*- elif p.type in ['char', 'uint8_t'] -*/
  /*# Lemmas and defs for unsigned 8-bit heap. #*/
  /*? update_t_def(heap_lemmas, 8, False) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 8) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 8) ?*/
  /*? heap_t_update_compose(heap_lemmas, 8) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 8) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 8) ?*/
  /*? cast_ucast_id_t(heap_lemmas, 8, False) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 8, False) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 8) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 8, False) ?*/
  /*? is_valid_update_t(heap_lemmas, 8, False, 8) ?*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, False, 16) ?*/
  /*- endif -*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, False, 32) ?*/
  /*- endif -*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 8, False, 64) ?*/
  /*- endif -*/

/*- elif p.type == 'int16_t' -*/
  /*# Lemmas and defs for signed 16-bit heap. #*/
  /*? update_t_def(heap_lemmas, 16, True) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 16) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 16) ?*/
  /*? heap_t_update_compose(heap_lemmas, 16) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 16) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 16) ?*/
  /*? cast_ucast_id_t(heap_lemmas, 16, True) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 16, True) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 16) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 16, True) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, True, 8) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 16, True, 16) ?*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, True, 32) ?*/
  /*- endif -*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, True, 64) ?*/
  /*- endif -*/

/*- elif p.type == 'uint16_t' -*/
  /*# Lemmas and defs for unsigned 16-bit heap. #*/
  /*? update_t_def(heap_lemmas, 16, False) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 16) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 16) ?*/
  /*? heap_t_update_compose(heap_lemmas, 16) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 16) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 16) ?*/
  /*? cast_ucast_id_t(heap_lemmas, 16, False) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 16, False) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 16) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 16, False) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, False, 8) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 16, False, 16) ?*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, False, 32) ?*/
  /*- endif -*/
  /*- if '64 word' in used_types or '64 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 16, False, 64) ?*/
  /*- endif -*/

/*- elif p.type == 'uint64_t' -*/
  /*# Lemmas and defs for unsigned 64-bit heap. #*/
  /*? update_t_def(heap_lemmas, 64, False) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 64) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 64) ?*/
  /*? heap_t_update_compose(heap_lemmas, 64) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 64) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 64) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 64, False) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 64) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 64, False) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, False, 8) ?*/
  /*- endif -*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, False, 16) ?*/
  /*- endif -*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, False, 32) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 64, False, 64) ?*/

/*- elif p.type == 'int64_t' -*/
  /*# Lemmas and defs for unsigned 64-bit heap. #*/
  /*? update_t_def(heap_lemmas, 64, True) ?*/
  /*? heap_t_update_preserves_inv(heap_lemmas, 64) ?*/
  /*? heap_t_update_equiv(heap_lemmas, 64) ?*/
  /*? heap_t_update_compose(heap_lemmas, 64) ?*/
  /*? getmr_heap_t_update(heap_lemmas, 64) ?*/
  /*? setmr_heap_t_update_reorder(heap_lemmas, 64) ?*/
  /*? heap_update_preserves_ptr_valid_t(heap_lemmas, 64, True) ?*/
  /*? of_int_via_ucast_t(heap_lemmas, 64) ?*/
  /*? update_t_preserves_inv(heap_lemmas, 64, True) ?*/
  /*- if '8 word' in used_types or '8 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, True, 8) ?*/
  /*- endif -*/
  /*- if '16 word' in used_types or '16 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, True, 16) ?*/
  /*- endif -*/
  /*- if '32 word' in used_types or '32 sword' in used_types -*/
    /*? is_valid_update_t(heap_lemmas, 64, True, 32) ?*/
  /*- endif -*/
  /*? is_valid_update_t(heap_lemmas, 64, True, 64) ?*/

/*- endif -*/

/*- endfor -*/
/*- endfor -*/

/*- for w1, have in have_heap.items() -*/
  /*- if have -*/

lemma heap_w/*? w1 ?*/_setmr[simp]: "heap_w/*? w1 ?*/ (setMR s i x) = heap_w/*? w1 ?*/ s"
  by (simp add:setMR_def)

    /*- for w2, have in have_heap.items() -*/
      /*- if have -*/
        /*- if w1 == w2 -*/
          /*- if ('%d sword' % w2) in used_types -*/
    lemma heap_w/*? w1 ?*/_update_s/*? w2 ?*/: "heap_w/*? w1 ?*/ (update_s/*? w2 ?*/ s p v) q = (if (ptr_coerce p) = q then scast v else heap_w/*? w1 ?*/ s q)"
      by (simp add:update_s/*? w2 ?*/_def)
          /*- endif -*/

          /*- if ('%d word' % w2) in used_types -*/
    lemma heap_w/*? w1 ?*/_update_u/*? w2 ?*/: "heap_w/*? w1 ?*/ (update_u/*? w2 ?*/ s p v) q = (if p = q then v else heap_w/*? w1 ?*/ s q)"
      by (simp add:update_u/*? w2 ?*/_def)
          /*- endif -*/
        /*- else -*/
          /*- if ('%d sword' % w2) in used_types -*/
    lemma heap_w/*? w1 ?*/_update_s/*? w2 ?*/[simp]: "heap_w/*? w1 ?*/ (update_s/*? w2 ?*/ s p v) q = heap_w/*? w1 ?*/ s q"
      by (simp add:update_s/*? w2 ?*/_def)
          /*- endif -*/

          /*- if ('%d word' % w2) in used_types -*/
    lemma heap_w/*? w1 ?*/_update_u/*? w2 ?*/[simp]: "heap_w/*? w1 ?*/ (update_u/*? w2 ?*/ s p v) q = heap_w/*? w1 ?*/ s q"
      by (simp add:update_u/*? w2 ?*/_def)
          /*- endif -*/
        /*- endif -*/
      /*- endif -*/
    /*- endfor -*/
  /*- endif -*/
/*- endfor -*/

/*- endif -*/
