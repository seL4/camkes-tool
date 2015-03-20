/*- if 'autocorres/seL4_GetIPCBuffer_wp.thy' not in included -*/
/*- do included.add('autocorres/seL4_GetIPCBuffer_wp.thy') -*/

/*- include 'autocorres/inv.thy' -*/

lemma seL4_GetIPCBuffer_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s0. \<lbrace>\<lambda>s. s = s0 \<and>
             globals_frame_intact s \<and>
             ipc_buffer_valid s\<rbrace>
          seL4_GetIPCBuffer'
        \<lbrace>\<lambda>r s. s = s0 \<and>
               r = ipc_buffer_ptr s\<rbrace>!"
  apply (rule allI)
  unfolding seL4_GetIPCBuffer'_def apply wp
  apply (clarsimp simp:inv_defs)
  done

/*- endif -*/
