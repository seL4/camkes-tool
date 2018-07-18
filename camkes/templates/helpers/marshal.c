/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

/*- from 'helpers/tls.c' import make_tls_symbols -*/

/*- macro show_input_parameter(p) -*/
    /*- if p.direction == 'in' -*/
        /*- if p.array -*/
            size_t /*? p.name ?*/_sz,
            /*- if p.type == 'string' -*/
                char **
            /*- else -*/
                const /*? macros.show_type(p.type) ?*/ *
            /*- endif -*/
        /*- elif p.type == 'string' -*/
            const char *
        /*- else -*/
            /*? macros.show_type(p.type) ?*/
        /*- endif -*/
        /*? p.name ?*/
    /*- else -*/
        /*- if p.array -*/
            /*- if p.direction == 'refin' -*/
                const
            /*- endif -*/
            size_t * /*? p.name ?*/_sz,
            /*- if p.type == 'string' -*/
                char ***
            /*- else -*/
                /*? macros.show_type(p.type) ?*/ **
            /*- endif -*/
        /*- elif p.type == 'string' -*/
            char **
        /*- else -*/
            /*- if p.direction == 'refin' -*/
                const
            /*- endif -*/
            /*? macros.show_type(p.type) ?*/ *
        /*- endif -*/
        /*? p.name ?*/
    /*- endif -*/
/*- endmacro -*/

/*- macro show_input_parameter_list(parameters, valid_directions) -*/
    /*- for p in parameters -*/
        /*? assert(p.direction in valid_directions) ?*/
        /*? show_input_parameter(p) ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    /*- if len(parameters) == 0 -*/
        void
    /*- endif -*/
/*- endmacro -*/

/*- macro err_if_buffer_length_exceeded(instance, interface, size, cur_offset, desired, target_name, parent_name, error_handler) -*/
    ERR_IF(/*? desired ?*/ > /*? size ?*/ - /*? cur_offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
        .type = CE_BUFFER_LENGTH_EXCEEDED,
        .instance = "/*? instance ?*/",
        .interface = "/*? interface ?*/",
        .description = "buffer exceeded while marshalling /*? target_name ?*/ in /*? parent_name ?*/",
        .current_length = /*? cur_offset ?*/,
        .target_length = /*? cur_offset ?*/ + /*? desired ?*/,
        }), ({
            return UINT_MAX;
    }));
/*- endmacro -*/

/*# Generates code for marshalling input parameters to an RPC invocation
  #     instance: Name of this component instance
  #     interface: Name of this interface
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     size: Length of the buffer; possibly not generation-time constant
  #     method_index: Index of this method in the containing interface
  #     methods_len: Total number of methods in this interface
  #     input_parameters: All input parameters to this method
  #     error_handler: Handler to invoke on error
  #     threads: List of threads in the interface
  #*/
/*- macro make_marshal_input_symbols(instance, interface, name, function, buffer, size, method_index, methods_len, input_parameters, error_handler, threads) -*/
    /*# Validate that our arguments are the correct type #*/
    /*? assert(isinstance(instance, six.string_types)) ?*/
    /*? assert(isinstance(interface, six.string_types)) ?*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(methods_len, six.integer_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/
    /*? assert(isinstance(error_handler, six.string_types)) ?*/
    /*? assert(isinstance(threads, list)) ?*/

    /*- set name_backup = name -*/
    /*- for p in input_parameters -*/
        /*- if p.direction == 'in' -*/
            /*- if p.array -*/
                /*? make_tls_symbols('size_t', '%s_%s_sz_from' % (name_backup, p.name), threads, False) ?*/
            /*- elif p.type != 'string' -*/
                /*? make_tls_symbols(macros.show_type(p.type), '%s_%s_from' % (name_backup, p.name), threads, False) ?*/
            /*- endif -*/
        /*- endif -*/
    /*- endfor -*/
    /*- set name = name_backup -*/

    /*- for p in input_parameters -*/
        /*? assert(p.direction in ['in', 'refin', 'inout']) ?*/
        /*- set offset = c_symbol('offset') -*/
        static unsigned /*? function ?*/_/*? p.name ?*/(unsigned /*? offset ?*/,
            /*? show_input_parameter(p) ?*/
        ) {

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /* Construct parameter pointers. We do this here to consolidate where we
         * are taking the address of local variables. In future, we need to avoid
         * doing this for verification.
         */
        /*- set ptr = c_symbol('ptr') -*/
        /*- set ptr_sz = c_symbol('ptr_sz') -*/
        /*- set ptr_str = c_symbol('ptr_str') -*/
        /*- set ptr_arr = c_symbol('ptr_arr') -*/
        /*- if p.direction == 'in' -*/
            /*- if p.array -*/
                size_t * /*? ptr_sz ?*/ = TLS_PTR(/*? name ?*/_/*? p.name ?*/_sz_from, /*? p.name ?*/_sz);
                * /*? ptr_sz ?*/ = /*? p.name ?*/_sz;
                /*- if p.type == 'string' -*/
                    char ** /*? ptr_arr ?*/ = /*? p.name ?*/;
                /*- else -*/
                    const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = /*? p.name ?*/;
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                const char * /*? ptr_str ?*/ = /*? p.name ?*/;
            /*- else -*/
                /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = TLS_PTR(/*? name ?*/_/*? p.name ?*/_from, /*? p.name ?*/);
                * /*? ptr ?*/ = /*? p.name ?*/;
            /*- endif -*/
        /*- else -*/
            /*- if p.array -*/
                const size_t * /*? ptr_sz ?*/ = /*? p.name ?*/_sz;
                /*- if p.type == 'string' -*/
                    char ** /*? ptr_arr ?*/ = * /*? p.name ?*/;
                /*- else -*/
                    const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = * /*? p.name ?*/;
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                const char * /*? ptr_str ?*/ = * /*? p.name ?*/;
            /*- else -*/
                const /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = /*? p.name ?*/;
            /*- endif -*/
        /*- endif -*/

        /*- if p.array -*/
            /*- set target = 'sizeof(* %s)' % ptr_sz -*/
            /*? err_if_buffer_length_exceeded(instance, interface, size, offset, target, p.name, name, error_handler) ?*/
            memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_sz ?*/, /*? target ?*/);
            /*? offset ?*/ += /*? target ?*/;
            /*- if p.type == 'string' -*/
                /*- set lcount = c_symbol() -*/
                for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ptr_sz ?*/; /*? lcount ?*/ ++) {
                    /*- set strlen = c_symbol('strlen') -*/
                    size_t /*? strlen ?*/ = strnlen(/*? ptr_arr ?*/[/*? lcount ?*/], /*? size ?*/ - /*? offset ?*/);
                    /*- set nulllen = '%s + 1' % strlen -*/
                    /*? err_if_buffer_length_exceeded(instance, interface, size, offset, nullen, p.name, name, error_handler) ?*/
                    /* If we didn't trigger an error, we now know this strcpy is safe. */
                    (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/[/*? lcount ?*/]);
                    /*? offset ?*/ += /*? nulllen ?*/;
                }
            /*- else -*/
                /*- set target = 'sizeof(%s[0]) * (* %s)' % (ptr_arr, ptr_sz) -*/
                /*? err_if_buffer_length_exceeded(instance, interface, size, offset, target, p.name, name, error_handler) ?*/
                memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/, /*? target ?*/);
                /*? offset ?*/ += /*? target ?*/
            /*- endif -*/
        /*- elif p.type == 'string' -*/
            /*- set strlen = c_symbol('strlen') -*/
            size_t /*? strlen ?*/ = strnlen(/*? ptr_str ?*/, /*? size ?*/ - /*? offset ?*/);
            /*- set nulllen = '%s + 1' % strlen -*/
            /*? err_if_buffer_length_exceeded(instance, interface, size, offset, nulllen, p.name, name, error_handler) ?*/
            /* If we didn't trigger an error, we now know this strcpy is safe. */
            (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_str ?*/);
            /*? offset ?*/ += /*? nulllen ?*/;
        /*- else -*/
            /*- set target = 'sizeof(* %s)' % ptr -*/
            /*? err_if_buffer_length_exceeded(instance, interface, size, offset, target, p.name, name, error_handler) ?*/
            memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr ?*/, /*? target ?*/);
            /*? offset ?*/ += /*? target ?*/;
        /*- endif -*/
        return /*? offset ?*/;
    }
    /*- endfor -*/

    /*- if methods_len > 1 -*/
        /*- set call = c_symbol('method_index') -*/
        static const /*? macros.type_to_fit_integer(methods_len) ?*/ /*? call ?*/ = /*? method_index ?*/;
    /*- endif -*/

    static unsigned /*? function ?*/(
    /*? show_input_parameter_list(input_parameters, ['in', 'refin', 'inout']) ?*/
    ) {

        /*- set length = c_symbol('length') -*/
        unsigned /*? length ?*/ = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if methods_len > 1 -*/
            /* Marshal the method index. */
            /*- set target = 'sizeof(%s)' % call -*/
            /*? err_if_buffer_length_exceeded(instance, interface, size, offset, target, p.name, name, error_handler) ?*/
            memcpy(/*? base ?*/, & /*? call ?*/, /*? target ?*/);
            /*? length ?*/ += /*? target ?*/;
        /*- endif -*/

        /* Marshal the parameters. */
        /*- for p in input_parameters -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
            /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? length ?*/,
            /*- if p.array -*/
                /*? p.name ?*/_sz,
            /*- endif -*/
            /*? p.name ?*/
            );
            if (unlikely(/*? length ?*/ == UINT_MAX)) {
                return UINT_MAX;
            }
        /*- endfor -*/

        assert(/*? length ?*/ <= /*? size ?*/ &&
            "uncaught buffer overflow while marshalling inputs for /*? name ?*/");

        return /*? length ?*/;
    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will marshal input parameters
  # function: Name of function to invoke
  # input_parameters: All input parameters to this method
  #*/
/*- macro call_marshal_input(function, input_parameters) -*/
    /*# Validate our arguments are the correct types #*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    /*? function ?*/(
    /*- for p in input_parameters -*/
        /*- if p.array -*/
            /*? p.name ?*/_sz,
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    )
/*- endmacro -*/


/*# Generates code for marshalling out parameters to an RPC invocation
  #     instance: Name of this component instance
  #     interface: Name of this interface
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     size: Length of the buffer; possibly not generation-time constant
  #     method_index: Index of this method in the containing interface
  #     output_parameters: All output parameters to this method
  #     return_type: Return type of this interface
  #     error_handler: Handler to invoke on error
  #     allow_trailing_data: Whether to ignore checks for remaining bytes after a message
  #*/
/*# Whether to ignore checks for remaining bytes after a message #*/
/*- macro make_unmarshal_output_symbols(instance, interface, name, function, buffer, size, method_index, output_parameters, return_type, error_handler, allow_trailing_data) -*/
    /*# Validate our argument types #*/
    /*? assert(isinstance(instance, six.string_types)) ?*/
    /*? assert(isinstance(interface, six.string_types)) ?*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/
    /*? assert(isinstance(error_handler, six.string_types)) ?*/
    /*? assert(isinstance(allow_trailing_data, bool)) ?*/

    /*- set ret_fn = c_symbol('ret_fn') -*/
    /*- if return_type is not none -*/
        /*- set offset = c_symbol('offset') -*/
        /*- set size = c_symbol('size') -*/
        /*- set ret = c_symbol('return') -*/
        static unsigned /*? function ?*/_/*? ret_fn ?*/(unsigned /*? size ?*/, unsigned /*? offset ?*/,
        /*? macros.show_type(return_type) ?*/ *
        /*? ret ?*/
        ) {

            /*- set base = c_symbol('buffer_base') -*/
            void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

            /* Unmarshal the return value. */
            /*- if return_type == 'string' -*/
                /*- set strlen = c_symbol('strlen') -*/
                size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
                ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
                    }), ({
                        return UINT_MAX;
                }));
                * /*? ret ?*/ = strdup(/*? base ?*/ + /*? offset ?*/);
                ERR_IF(* /*? ret ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_ALLOCATION_FAILURE,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "out of memory while unmarshalling return value for /*? name ?*/",
                    .alloc_bytes = /*? strlen ?*/ + 1,
                    }), ({
                        return UINT_MAX;
                }));
                /*? offset ?*/ += /*? strlen ?*/ + 1;
            /*- else -*/
                ERR_IF(/*? offset ?*/ + sizeof(* /*? ret ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling return value for /*? name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? offset ?*/ + sizeof(* /*? ret ?*/),
                    }), ({
                        return UINT_MAX;
                }));
                memcpy(/*? ret ?*/, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? ret ?*/));
                /*? offset ?*/ += sizeof(* /*? ret ?*/);
            /*- endif -*/

            return /*? offset ?*/;
        }
    /*- endif -*/
    /*- for p in output_parameters -*/
        /*- set size = c_symbol('size') -*/
        /*- set offset = c_symbol('offset') -*/
        static unsigned /*? function ?*/_/*? p.name ?*/(unsigned /*? size ?*/, unsigned /*? offset ?*/,
        /*- if p.array -*/
            size_t * /*? p.name ?*/_sz,
            /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
        /*- else -*/
            /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
        /*- endif -*/
        ) {

            /*- set base = c_symbol('buffer_base') -*/
            void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

            /*- if p.array -*/
                ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? offset ?*/ + sizeof(* /*? p.name ?*/_sz),
                    }), ({
                        return UINT_MAX;
                }));
                memcpy(/*? p.name ?*/_sz, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? p.name ?*/_sz));
                /*? offset ?*/ += sizeof(* /*? p.name ?*/_sz);
                /*- if p.direction == 'inout' -*/
                    /*- if p.type == 'string' -*/
                        /*- set mcount = c_symbol() -*/
                        for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
                            free((* /*? p.name ?*/)[/*? mcount ?*/]);
                        }
                    /*- endif -*/
                    free(* /*? p.name ?*/);
                /*- endif -*/
                /*- if p.type == 'string' -*/
                    * /*? p.name ?*/ = malloc(sizeof(char*) * (* /*? p.name ?*/_sz));
                    ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_ALLOCATION_FAILURE,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                        .alloc_bytes = sizeof(char*) * (* /*? p.name ?*/_sz),
                        }), ({
                            return UINT_MAX;
                    }));
                /*- else -*/
                    * /*? p.name ?*/ = malloc(sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
                    ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_ALLOCATION_FAILURE,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                        .alloc_bytes = sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
                        }), ({
                            return UINT_MAX;
                    }));
                /*- endif -*/
                /*- if p.type == 'string' -*/
                    /*- set lcount = c_symbol() -*/
                    for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? p.name ?*/_sz; /*? lcount ?*/ ++) {
                        /*- set strlen = c_symbol('strlen') -*/
                        size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
                        ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
                            .type = CE_MALFORMED_RPC_PAYLOAD,
                            .instance = "/*? instance ?*/",
                            .interface = "/*? interface ?*/",
                            .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                            .length = /*? size ?*/,
                            .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
                            }), ({
                                /*- set mcount = c_symbol() -*/
                                for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                                    free((* /*? p.name ?*/)[/*? mcount ?*/]);
                                }
                                free(* /*? p.name ?*/);
                                return UINT_MAX;
                        }));
                        /* If we didn't trigger an error, we now know this strdup is safe. */
                        (* /*? p.name ?*/)[/*? lcount ?*/] = strdup(/*? base ?*/ + /*? offset ?*/);
                        ERR_IF((* /*? p.name ?*/)[/*? lcount ?*/] == NULL, /*? error_handler ?*/, ((camkes_error_t){
                            .type = CE_ALLOCATION_FAILURE,
                            .instance = "/*? instance ?*/",
                            .interface = "/*? interface ?*/",
                            .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                            .alloc_bytes = /*? strlen ?*/ + 1,
                            }), ({
                                /*- set mcount = c_symbol() -*/
                                for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < /*? lcount ?*/; /*? mcount ?*/ ++) {
                                    free((* /*? p.name ?*/)[/*? mcount ?*/]);
                                }
                                free(* /*? p.name ?*/);
                                return UINT_MAX;
                        }));
                        /*? offset ?*/ += /*? strlen ?*/ + 1;
                    }
                /*- else -*/
                    ERR_IF(/*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_MALFORMED_RPC_PAYLOAD,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                        .length = /*? size ?*/,
                        .current_index = /*? offset ?*/ + sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz),
                        }), ({
                            free(* /*? p.name ?*/);
                            return UINT_MAX;
                    }));
                    memcpy((* /*? p.name ?*/), /*? base ?*/ + /*? offset ?*/, sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz));
                    /*? offset ?*/ += sizeof((* /*? p.name ?*/)[0]) * (* /*? p.name ?*/_sz);
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*- if p.direction == 'inout' -*/
                    free(* /*? p.name ?*/);
                /*- endif -*/
                /*- set strlen = c_symbol('strlen') -*/
                size_t /*? strlen ?*/ = strnlen(/*? base ?*/ + /*? offset ?*/, /*? size ?*/ - /*? offset ?*/);
                ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? offset ?*/ + /*? strlen ?*/ + 1,
                    }), ({
                        return UINT_MAX;
                }));
                * /*? p.name ?*/ = strdup(/*? base ?*/ + /*? offset ?*/);
                ERR_IF(* /*? p.name ?*/ == NULL, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_ALLOCATION_FAILURE,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "out of memory while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                    .alloc_bytes = /*? strlen ?*/ + 1,
                    }), ({
                        return UINT_MAX;
                }));
                /*? offset ?*/ += /*? strlen ?*/ + 1;
            /*- else -*/
                ERR_IF(/*? offset ?*/ + sizeof(* /*? p.name ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_MALFORMED_RPC_PAYLOAD,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "truncated message encountered while unmarshalling /*? p.name ?*/ in /*? name ?*/",
                    .length = /*? size ?*/,
                    .current_index = /*? offset ?*/ + sizeof(* /*? p.name ?*/),
                    }), ({
                        return UINT_MAX;
                }));
                memcpy(/*? p.name ?*/, /*? base ?*/ + /*? offset ?*/, sizeof(* /*? p.name ?*/));
                /*? offset ?*/ += sizeof(* /*? p.name ?*/);
            /*- endif -*/

            return /*? offset ?*/;
        }
    /*- endfor -*/

    static int
    /*? function ?*/(
    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/
    /*- if return_type is not none or len(output_parameters) > 0 -*/
        ,
    /*- endif -*/
    /*- set ret = c_symbol('return') -*/
    /*- if return_type is not none -*/
        /*? macros.show_type(return_type) ?*/ *
        /*? ret ?*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*- for p in output_parameters -*/
        /*- if p.array -*/
            size_t * /*? p.name ?*/_sz,
            /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
        /*- else -*/
            /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
        /*- endif -*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    ) {

        /*- set length = c_symbol('length') -*/
        unsigned /*? length ?*/ UNUSED = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if return_type is not none -*/
            /*? length ?*/ = /*? function ?*/_/*? ret_fn ?*/(/*? size ?*/, /*? length ?*/,
            /*? ret ?*/
            );
            if (unlikely(/*? length ?*/ == UINT_MAX)) {
                return -1;
            }
        /*- endif -*/

        /* Unmarshal the parameters. */
        /*- for index, p in enumerate(output_parameters) -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
            /*? length ?*/ = /*? function ?*/_/*? p.name ?*/(/*? size ?*/, /*? length ?*/,
            /*- if p.array -*/
                /*? p.name ?*/_sz,
            /*- endif -*/
            /*? p.name ?*/
            );
            if (unlikely(/*? length ?*/ == UINT_MAX)) {
                /*- if return_type == 'string' -*/
                    free(* /*? ret ?*/);
                /*- endif -*/
                /*- for q in itertools.islice(output_parameters, index) -*/
                    /*- if q.array -*/
                        /*- if q.type == 'string' -*/
                            /*- set mcount = c_symbol() -*/
                            for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? q.name ?*/_sz; /*? mcount ?*/ ++) {
                                free((* /*? q.name ?*/)[/*? mcount ?*/]);
                            }
                        /*- endif -*/
                        free(* /*? q.name ?*/);
                    /*- elif q.type == 'string' -*/
                        free(* /*? q.name ?*/);
                    /*- endif -*/
                /*- endfor -*/
                return -1;
            }
        /*- endfor -*/

        /*- if not allow_trailing_data -*/
        ERR_IF(ROUND_UP_UNSAFE(/*? length ?*/, sizeof(seL4_Word)) != /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
            .type = CE_MALFORMED_RPC_PAYLOAD,
            .instance = "/*? instance ?*/",
            .interface = "/*? interface ?*/",
            .description = "excess trailing bytes after unmarshalling parameters for /*? name ?*/",
            .length = /*? size ?*/,
            .current_index = /*? length ?*/,
            }), ({
                /*- if return_type == 'string' -*/
                    free(* /*? ret ?*/);
                /*- endif -*/
                /*- for p in output_parameters -*/
                    /*- if p.array -*/
                        /*- if p.type == 'string' -*/
                            /*- set mcount = c_symbol() -*/
                            for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? p.name ?*/_sz; /*? mcount ?*/ ++) {
                                free((* /*? p.name ?*/)[/*? mcount ?*/]);
                            }
                        /*- endif -*/
                        free(* /*? p.name ?*/);
                    /*- elif p.type == 'string' -*/
                        free(* /*? p.name ?*/);
                    /*- endif -*/
                /*- endfor -*/
                return -1;
        }));
    /*- endif -*/

    return 0;
    }
/*- endmacro -*/


/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # size: Name of a variable storing the byte length of the message
  # output_parameters: All output parameters to this method
  # return_type: Return type of this interface
  # ret_ptr: Pointer for the return value
  #*/
/*- macro call_unmarshal_output(function, size, output_parameters, return_type, ret_ptr) -*/
    /*# Validate the types of our arguments #*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    /*? function ?*/(
    /*? size ?*/
    /*- if return_type is not none or len(output_parameters) > 0 -*/
        ,
    /*- endif -*/
    /*- if return_type is not none -*/
        /*? ret_ptr ?*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*- for p in output_parameters -*/
    /*- if p.array -*/
        /*? p.name ?*/_sz,
    /*- endif -*/
    /*? p.name ?*/
    /*- if not loop.last -*/
        ,
    /*- endif -*/
    /*- endfor -*/
    )
/*- endmacro -*/
