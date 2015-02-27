/*#
 *# Copyright 2014, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

/*# Thread-local storage functionality. This is not a standalone C file. You
 *# are expected to include this from a template, after having set the
 *# variables 'type', 'name' and 'threads' to determine the behaviour below.
 *# See examples in the templates themselves.
 #*/

/*- for index in threads -*/
    /*- if array -*/
        static size_t /*? name ?*/_sz_/*? index ?*/;
        /*# The existence of this pointer is rather unpleasant. We need to
         *# return a reference to the static array that, itself, needs to be a
         *# global. Naturally this is all once again necessitated by
         *# verification.
         #*/
        static /*? type ?*/ * /*? name ?*/_ptr_/*? index ?*/;
    /*- endif -*/
    static /*? type ?*/ /*? name ?*/_/*? index ?*/
    /*- if array -*/
        /*# Assume this array is for some IPC-transferred data and therefore
         *# cannot be bigger than the IPC buffer.
        #*/
        [seL4_MsgMaxLength * sizeof(seL4_Word) / sizeof(/*? type ?*/)]
    /*- endif -*/
    ;
/*- endfor -*/

/*- if array -*/
    static size_t *get_/*? name ?*/_sz(void) __attribute__((unused));
    static size_t *get_/*? name ?*/_sz(void) {
        switch(camkes_get_tls()->thread_index) {
            /*- for index in threads -*/
                case /*? index ?*/:
                    return & /*? name ?*/_sz_/*? index ?*/;
            /*- endfor -*/
            default:
                assert(!"invalid thread index");
                abort();
        }
    }
/*- endif -*/

static /*? type ?*/ *
/*- if array -*/
    *
/*- endif -*/
get_/*? name ?*/(void) __attribute__((unused));
static /*? type ?*/ *
/*- if array -*/
    *
/*- endif -*/
get_/*? name ?*/(void) {
    switch (camkes_get_tls()->thread_index) {
        /*- for index in threads -*/
            case /*? index ?*/:
                /*- if array -*/
                    /*? name ?*/_ptr_/*? index ?*/ = /*? name ?*/_/*? index ?*/;
                    return & /*? name ?*/_ptr_/*? index ?*/;
                /*- else -*/
                    return & /*? name ?*/_/*? index ?*/;
                /*- endif -*/
        /*- endfor -*/
        default:
            assert(!"invalid thread index");
            abort();
    }
}
