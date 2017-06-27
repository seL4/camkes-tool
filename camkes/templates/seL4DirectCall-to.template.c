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

/* This template is intentionally blank. It is intended to be used when
 * components are hosted in the same address space and, hence, no connecting
 * glue code is actually required. Note, that connecting the relevant symbols
 * at link-time relies on extra logic in the Makefile template.
 */

/*- for end in me.parent.from_ends + me.parent.to_ends -*/
  /*- if end.instance.address_space != me.instance.address_space -*/
    /*? raise(TemplateError('%s.%s participating in connection %s is not in address space \'%s\'' % (end.instance.name, end.interface.name, me.parent.name, me.instance.address_space), end)) ?*/
  /*- endif -*/
/*- endfor -*/
