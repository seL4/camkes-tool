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

theory "/*? thy ?*/" imports
  "~~/../l4v/tools/autocorres/AutoCorres"
  "~~/../l4v/lib/LemmaBucket"
  "~~/../l4v/lib/WordBitwiseSigned"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

/*# install_code.thy expects the thy variable to have a specific relationship
 *# to the underlying C file we want to install.
 #*/
/*- set thy = re.sub('(.*)_base', '\\1', thy) -*/
/*- include 'autocorres/install_code.thy' -*/

end
