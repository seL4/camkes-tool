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

/*- if 'autocorres/debug_abbrevs.thy' not in included -*/
/*- do included.add('autocorres/debug_abbrevs.thy') -*/

(** TPP: condense = True *)
/*# This theory fragment contains abbreviations that are only useful when
 *# debugging generated theories. Note that these abbreviations are only
 *# emitted in debugging mode.
 #*/

/*- if options.verbosity >= 2 -*/

/*- macro ucast_abbrev(f, t) -*/
abbreviation "ucast_/*- if f.endswith('sword') -*/s/*- endif -*//*? f.split()[0] ?*/_to_/*- if t.endswith('sword') -*/s/*- endif -*//*? t.split()[0] ?*/ \<equiv> (ucast::/*? f ?*/ \<Rightarrow> /*? t ?*/)"
/*- endmacro -*/

/*- macro scast_abbrev(f, t) -*/
abbreviation "scast_/*- if f.endswith('sword') -*/s/*- endif -*//*? f.split()[0] ?*/_to_/*- if t.endswith('sword') -*/s/*- endif -*//*? t.split()[0] ?*/ \<equiv> (scast::/*? f ?*/ \<Rightarrow> /*? t ?*/)"
/*- endmacro -*/

/*- macro ptr_coerce_abbrev(f, t) -*/
abbreviation "ptr_coerce_/*- if f.endswith('sword') -*/s/*- endif -*//*? f.split()[0] ?*/_to_/*- if t.endswith('sword') -*/s/*- endif -*//*? t.split()[0] ?*/ \<equiv> (ptr_coerce::/*? f ?*/ ptr \<Rightarrow> /*? t ?*/ ptr)"
/*- endmacro -*/

/*- macro of_int_abbrev(t) -*/
abbreviation "of_int_to_/*- if t.endswith('sword') -*/s/*- endif -*//*? t.split()[0] ?*/ \<equiv> (of_int::int \<Rightarrow> /*? t ?*/)"
/*- endmacro -*/

/*- macro sint_abbrev(f) -*/
abbreviation "sint_/*- if f.endswith('sword') -*/s/*- endif -*//*? f.split()[0] ?*/ \<equiv> (sint::/*? f ?*/ \<Rightarrow> int)"
/*- endmacro -*/

/*- macro uint_abbrev(f) -*/
abbreviation "uint_/*- if f.endswith('sword') -*/s/*- endif -*//*? f.split()[0] ?*/ \<equiv> (uint::/*? f ?*/ \<Rightarrow> int)"
/*- endmacro -*/

/*- for from_width in [8, 16, 32, 64] -*/
  /*- for from_signed in [True, False] -*/
    /*- set from_type = '%d %sword' % (from_width, 's' if from_signed else '') -*/
    /*- for to_width in [8, 16, 32, 64] -*/
      /*- for to_signed in [True, False] -*/
        /*- set to_type = '%d %sword' % (to_width, 's' if to_signed else '') -*/
        /*? ucast_abbrev(from_type, to_type) ?*/
        /*? ptr_coerce_abbrev(from_type, to_type) ?*/
        /*- if from_signed -*/
          /*? scast_abbrev(from_type, to_type) ?*/
        /*- endif -*/
      /*- endfor -*/
    /*- endfor -*/
    /*? of_int_abbrev(from_type) ?*/ /*# Yes, I know the variable's called 'from_type'... #*/
    /*- if from_signed -*/
      /*? sint_abbrev(from_type) ?*/
    /*- endif -*/
    /*? uint_abbrev(from_type) ?*/
  /*- endfor -*/
/*- endfor -*/

(* Make scast only valid for signed words. *)
abbreviation "BROKEN_SCAST \<equiv> scast"
abbreviation "scast\<^sub>' \<equiv> (scast::'a::len sword \<Rightarrow> 'b::len word)"
definition
  scast :: "'a::len sword \<Rightarrow> 'b::len word"
where [simp]:
  "scast \<equiv> Word.scast"

/*- endif -*/
(** TPP: condense = False *)

/*- endif -*/
