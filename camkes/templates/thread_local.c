/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/*# Thread-local storage functionality. This is not a standalone C file. You
 *# are expected to include this from a template, after having set the
 *# variables 'type', 'name' and 'threads' to determine the behaviour below.
 *# See examples in the templates themselves.
 #*/

/* The TLS_PTR macro is for acquiring a pointer to a local variable. The first
 * argument is the corresponding TLS global and the second is the local
 * variable you are taking the address of. The purpose of this abstraction is
 * to allow for varying TLS models.
 */

#ifdef CONFIG_CAMKES_TLS_STANDARD

  #ifndef TLS_PTR
    #define TLS_PTR(tls_var, name) (&(name))
  #endif

#elif defined(CONFIG_CAMKES_TLS_PTG)

  #ifndef TLS_PTR
    #define TLS_PTR(tls_var, name) (get_##tls_var())
  #endif

#else

  #error undefined TLS model

#endif

/*- for index in threads -*/
    /*- if array -*/
        /*# The existence of this pointer is rather unpleasant. We need to
         *# return a reference to the static array that, itself, needs to be a
         *# global. Naturally this is all once again necessitated by
         *# verification.
         #*/
        static /*? type ?*/ * /*? name ?*/_ptr_/*? index ?*/ UNUSED;
    /*- endif -*/
    static /*? type ?*/ /*? name ?*/_/*? index ?*/
    /*- if array -*/
        /*# Assume this array is for some IPC-transferred data and therefore
         *# cannot be bigger than the IPC buffer.
        #*/
        [seL4_MsgMaxLength * sizeof(seL4_Word) / sizeof(/*? type ?*/)]
    /*- endif -*/
    UNUSED;
/*- endfor -*/

static /*? type ?*/ *
/*- if array -*/
    *
/*- endif -*/
get_/*? name ?*/(void) UNUSED;
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
