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
            ERR_IF(/*? offset ?*/ + sizeof(* /*? ptr_sz ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_BUFFER_LENGTH_EXCEEDED,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
                .current_length = /*? offset ?*/,
                .target_length = /*? offset ?*/ + sizeof(* /*? ptr_sz ?*/),
                }), ({
                    return UINT_MAX;
            }));
            memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_sz ?*/, sizeof(* /*? ptr_sz ?*/));
            /*? offset ?*/ += sizeof(* /*? ptr_sz ?*/);
            /*- if p.type == 'string' -*/
                /*- set lcount = c_symbol() -*/
                for (int /*? lcount ?*/ = 0; /*? lcount ?*/ < * /*? ptr_sz ?*/; /*? lcount ?*/ ++) {
                    /*- set strlen = c_symbol('strlen') -*/
                    size_t /*? strlen ?*/ = strnlen(/*? ptr_arr ?*/[/*? lcount ?*/], /*? size ?*/ - /*? offset ?*/);
                    ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
                        .type = CE_BUFFER_LENGTH_EXCEEDED,
                        .instance = "/*? instance ?*/",
                        .interface = "/*? interface ?*/",
                        .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
                        .current_length = /*? offset ?*/,
                        .target_length = /*? offset ?*/ + /*? strlen ?*/ + 1,
                        }), ({
                        return UINT_MAX;
                    }));
                    /* If we didn't trigger an error, we now know this strcpy is safe. */
                    (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/[/*? lcount ?*/]);
                    /*? offset ?*/ += /*? strlen ?*/ + 1;
                }
            /*- else -*/
                ERR_IF(/*? offset ?*/ + sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                    .type = CE_BUFFER_LENGTH_EXCEEDED,
                    .instance = "/*? instance ?*/",
                    .interface = "/*? interface ?*/",
                    .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
                    .current_length = /*? offset ?*/,
                    .target_length = /*? offset ?*/ + sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/),
                    }), ({
                        return UINT_MAX;
                }));
                memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_arr ?*/, sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/));
                /*? offset ?*/ += sizeof(/*? ptr_arr ?*/[0]) * (* /*? ptr_sz ?*/);
            /*- endif -*/
        /*- elif p.type == 'string' -*/
            /*- set strlen = c_symbol('strlen') -*/
            size_t /*? strlen ?*/ = strnlen(/*? ptr_str ?*/, /*? size ?*/ - /*? offset ?*/);
            ERR_IF(/*? strlen ?*/ >= /*? size ?*/ - /*? offset ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_BUFFER_LENGTH_EXCEEDED,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
                .current_length = /*? offset ?*/,
                .target_length = /*? offset ?*/ + /*? strlen ?*/ + 1,
                }), ({
                    return UINT_MAX;
            }));
            /* If we didn't trigger an error, we now know this strcpy is safe. */
            (void)strcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr_str ?*/);
            /*? offset ?*/ += /*? strlen ?*/ + 1;
        /*- else -*/
            ERR_IF(/*? offset ?*/ + sizeof(* /*? ptr ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_BUFFER_LENGTH_EXCEEDED,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "buffer exceeded while marshalling /*? p.name ?*/ in /*? name ?*/",
                .current_length = /*? offset ?*/,
                .target_length = /*? offset ?*/ + sizeof(* /*? ptr ?*/),
                }), ({
                    return UINT_MAX;
                }));
            memcpy(/*? base ?*/ + /*? offset ?*/, /*? ptr ?*/, sizeof(* /*? ptr ?*/));
            /*? offset ?*/ += sizeof(* /*? ptr ?*/);
        /*- endif -*/
        return /*? offset ?*/;
    }
    /*- endfor -*/

    /*- if methods_len > 1 -*/
        /*- set call = c_symbol('method_index') -*/
        static const
        /*- if methods_len <= 2 ** 8 -*/
            uint8_t
        /*- elif methods_len <= 2 ** 16 -*/
            uint16_t
        /*- elif methods_len <= 2 ** 32 -*/
            uint32_t
        /*- elif methods_len <= 2 ** 64 -*/
            uint64_t
        /*- else -*/
            /*? raise(TemplateError('too many methods in interface %s' % name)) ?*/
        /*- endif -*/
        /*? call ?*/ = /*? method_index ?*/;
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
            ERR_IF(/*? length ?*/ + sizeof(/*? call ?*/) > /*? size ?*/, /*? error_handler ?*/, ((camkes_error_t){
                .type = CE_BUFFER_LENGTH_EXCEEDED,
                .instance = "/*? instance ?*/",
                .interface = "/*? interface ?*/",
                .description = "buffer exceeded while marshalling method index for /*? name ?*/",
                .current_length = /*? length ?*/,
                .target_length = /*? length ?*/ + sizeof(/*? call ?*/),
                }), ({
                    return UINT_MAX;
            }));
            memcpy(/*? base ?*/, & /*? call ?*/, sizeof(/*? call ?*/));
            /*? length ?*/ += sizeof(/*? call ?*/);
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
