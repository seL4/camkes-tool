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

/*- if 'autocorres/camkes_get_tls_wp.thy' not in included -*/
/*- do included.add('autocorres/camkes_get_tls_wp.thy') -*/

/*- include 'autocorres/inv.thy' -*/
/*- include 'autocorres/seL4_GetIPCBuffer_wp.thy' -*/

lemma camkes_get_tls_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s0. \<lbrace>\<lambda>s. s = s0 \<and> inv s\<rbrace>
          camkes_get_tls'
        \<lbrace>\<lambda>r s. s = s0 \<and> r = tls_ptr s\<rbrace>!"
  apply (rule allI)
  unfolding camkes_get_tls'_def
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:tls_ptr_def ipc_buffer_ptr_def)
  done

/*- endif -*/
