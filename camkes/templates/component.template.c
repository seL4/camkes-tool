/*#
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 #*/

/*# This template exists as backwards compatiblity for the Make based build system that is not
  # going to be updated to support different environments. As such this template continues
  # building the C environment with the common environment into a single file.
  # This wrapping template can be removed once the Make based build system is removed #*/

/*# Include the common generated C code we need for every component. This is a workaround
    for not having additional template targets for the component yet #*/
/*- include 'component.common.c' -*/

/*# Currently we assume the one and only C environment and include that directly here,
    against because we currently must generate a single C file for the component template #*/
/*- include 'component.environment.c' -*/
