/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdbool.h>
#include <utils/util.h>

/*# This template assumes that the connector will only be used inside the composition block of a component, i.e. intra-component and not inter-component #*/

/*# Grab the list of DTB paths that from the configuration #*/
/*- set paths_list = configuration[me.instance.name].get('fdt_bind_driver_paths') -*/

/*- if paths_list is none -*/
    /*# Raise a fault, alerting the user to supply the proper configuration #*/
    /*? raise(TemplateError('Missing paths list! Create an attribute "paths" for the interface with a list of devicetree paths for the devices that you wish to initialise.')) ?*/
/*- endif -*/
/*# Sanity check #*/

/*- if not isinstance(paths_list, (tuple, list)) -*/
    /*? raise(TemplateError('Attribute %s.paths should be a list of devicetree paths!' % (me.interface.name))) ?*/
/*- endif -*/

/*# Walk through the list of paths and create a string for each path #*/
/*- for path in paths_list -*/
    /*- set path_var_name = '%s_path_%d' % (me.interface.name, loop.index0) -*/
    static char * /*? path_var_name ?*/ = "/*? path ?*/";
    USED SECTION("_hardware_init") char ** /*? path_var_name ?*/_ptr = &/*? path_var_name ?*/;
/*- endfor -*/
