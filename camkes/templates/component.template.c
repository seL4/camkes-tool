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

/*# Include the common generated C code we need for every component. This is a workaround
    for not having additional template targets for the component yet #*/
/*- include 'component.common.c' -*/

/*# Currently we assume the one and only C environment and include that directly here,
    against because we currently must generate a single C file for the component template #*/
/*- include 'component.environment.c' -*/
