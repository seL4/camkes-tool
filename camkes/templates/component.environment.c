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

/* include generated camkes component header. This currenlty has the prototypes
 * for the init functions */
#include <camkes.h>

int component_control_main() {
    /*- set result = c_symbol() -*/
    int /*? result ?*/;

    /*- if options.fsupport_init -*/
        if (pre_init) {
            pre_init();
        }
    /*- endif -*/

    /* we call pre_init_interface_sync in all circumstances, even if we do not support
     * init, as the implementation already has an internal guard for init support and
     * so the function will just do nothing without init support. Always calling it
     * provides a bit more flexibility in the future, and is consistent with the
     * post_init version which *does* do something even if we do not support init
     */
    /*? result ?*/ = pre_init_interface_sync();
    if (/*? result ?*/) {
        return /*? result ?*/;
    }

    /*- if options.fsupport_init -*/
        if (post_init) {
            post_init();
        }
    /*- endif -*/

    /*? result ?*/ = post_init_interface_sync();
    if (/*? result ?*/) {
        return /*? result ?*/;
    }

    /*- if me.type.control -*/
        return run();
    /*- else -*/
        return 0;
    /*- endif -*/
}

