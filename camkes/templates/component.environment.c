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

#include <camkes.h>
#include <camkes/init.h>

int component_control_main() {
    int error;

    if (pre_init) {
        pre_init();
    }

    /* we call pre_init_interface_sync in all circumstances, even if we do not support
     * init, as the implementation already has an internal guard for init support and
     * so the function will just do nothing without init support. Always calling it
     * provides a bit more flexibility in the future, and is consistent with the
     * post_init version which *does* do something even if we do not support init
     */
    error = pre_init_interface_sync();
    if (error) {
        return error;
    }

    if (post_init) {
        post_init();
    }

    error = post_init_interface_sync();
    if (error) {
        return error;
    }

    /*- if me.type.control -*/
        return run();
    /*- else -*/
        return 0;
    /*- endif -*/
}

