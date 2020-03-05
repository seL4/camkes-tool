/*
 * Copyright 2020, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <assert.h>
#include <stdbool.h>
#include <utils/util.h>

/*# This template assumes that the connector will only be used inside the composition block of a component, i.e. intra-component and not inter-component #*/

/*# Grab the list of DTB paths that from the configuration #*/
/*- set configuration_name = '%s.%s' % (me.instance.name, me.interface.name) -*/
/*- set paths_list = configuration[configuration_name].get('paths') -*/

/*- if paths_list is none -*/
    /*# Raise a fault, alerting the user to supply the proper configuration #*/
    /*? raise(TemplateError('Missing paths list! Create an attribute "paths" for the interface with a list of devicetree paths for the devices that you wish to initialise.')) ?*/
/*- endif -*/
/*# Sanity check #*/
/*- if not isinstance(paths_list, tuple) -*/
    /*? raise(TemplateError('Attribute %s.paths should be a list of devicetree paths!' % (me.interface.name))) ?*/
/*- endif -*/

/*# Walk through the list of paths and create a string for each path #*/
/*- for path in paths_list -*/
    /*- set path_var_name = '%s_path_%d' % (me.interface.name, loop.index0) -*/
    static char * /*? path_var_name ?*/ = "/*? path ?*/";
    USED SECTION("_hardware_init") char ** /*? path_var_name ?*/_ptr = &/*? path_var_name ?*/;
/*- endfor -*/
