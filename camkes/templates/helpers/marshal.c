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
/*- endmacro -*/

/*- macro show_output_parameter(p) -*/
    /*- if p.array -*/
        size_t * /*? p.name ?*/_sz,
        /*? macros.show_type(p.type) ?*/ ** /*? p.name ?*/
    /*- else -*/
        /*? macros.show_type(p.type) ?*/ * /*? p.name ?*/
    /*- endif -*/
/*- endmacro -*/

/*- macro show_output_parameter_list(parameters) -*/
    /*- for p in parameters -*/
        /*? show_output_parameter(p) ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
/*- endmacro -*/

/*# Generates code for marshalling input parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     size: Length of the buffer; possibly not generation-time constant
  #     method_index: Index of this method in the containing interface
  #     methods_len: Total number of methods in this interface
  #     input_parameters: All input parameters to this method
  #*/
/*- macro make_marshal_input_symbols(name, function, buffer, size, method_index, methods_len, input_parameters) -*/
    /*# Validate that our arguments are the correct type #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(methods_len, six.integer_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    static unsigned /*? function ?*/(
    /*? show_input_parameter_list(input_parameters, ['in', 'refin', 'inout']) ?*/
    /*- if len(input_parameters) == 0 -*/
        void
    /*- endif -*/
    ) {

        /*- set offset = c_symbol('offset') -*/
        unsigned /*? offset ?*/ = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if methods_len > 1 -*/
            /* Marshal the method index. */
            /*- set call = c_symbol('method_index') -*/
            /*? macros.type_to_fit_integer(methods_len) ?*/ /*? call ?*/ = /*? method_index ?*/;
            MARSHAL_PARAM(&/*? call ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "method_index");
        /*- endif -*/

        /* Marshal the parameters. */
        /*- for p in input_parameters -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
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
                    size_t * /*? ptr_sz ?*/ = &/*? p.name ?*/_sz;
                    * /*? ptr_sz ?*/ = /*? p.name ?*/_sz;
                    /*- if p.type == 'string' -*/
                        char ** /*? ptr_arr ?*/ = /*? p.name ?*/;
                    /*- else -*/
                        const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = /*? p.name ?*/;
                    /*- endif -*/
                /*- elif p.type == 'string' -*/
                    const char * /*? ptr_str ?*/ = /*? p.name ?*/;
                /*- else -*/
                    /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = &/*? p.name ?*/;
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
                /*- if p.type == 'string' -*/
                    /*? offset ?*/ = MARSHAL_STRING_ARRAY_PARAM(/*? ptr_arr ?*/, /*? ptr_sz ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
                /*- else -*/
                    /*? offset ?*/ = MARSHAL_ARRAY_PARAM(/*? ptr_arr ?*/, /*? ptr_sz ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*? offset ?*/ = MARSHAL_STRING_PARAM(/*? ptr_str ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/");
            /*- else -*/
                /*? offset ?*/ = MARSHAL_PARAM(/*? ptr ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/");
            /*- endif -*/
        /*- endfor -*/

        assert(/*? offset ?*/ <= /*? size ?*/ &&
            "uncaught buffer overflow while marshalling inputs for /*? name ?*/");

        return /*? offset ?*/;
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
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     method_index: Index of this method in the containing interface
  #     output_parameters: All output parameters to this method
  #     return_type: Return type of this interface
  #     allow_trailing_data: Whether to ignore checks for remaining bytes after a message
  #*/
/*# Whether to ignore checks for remaining bytes after a message #*/
/*- macro make_unmarshal_output_symbols(name, function, buffer, method_index, output_parameters, return_type, allow_trailing_data) -*/
    /*# Validate our argument types #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/
    /*? assert(isinstance(allow_trailing_data, bool)) ?*/

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

    /*? show_output_parameter_list(output_parameters) ?*/
    ) {

        /*- set offset = c_symbol('offset') -*/
        unsigned /*? offset ?*/ UNUSED = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if return_type is not none -*/
            /* Unmarshal the return value. */
            /*- if return_type == 'string' -*/
                /*? offset ?*/ = UNMARSHAL_STRING_PARAM(/*? ret ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "return value", ({return -1;}))
            /*- else -*/
                /*? offset ?*/ = UNMARSHAL_PARAM(/*? ret ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "return value", ({return -1;}))
            /*- endif -*/
        /*- endif -*/

        /* Unmarshal the parameters. */
        /*- for index, p in enumerate(output_parameters) -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
            /*- if p.array -*/
                /*- if p.direction == 'inout' -*/
                    /*- if p.type == 'string' -*/
                        /* At this point /*? p.name ?*/_sz should still contain the old size */
                        for (int i = 0; i < * /*? p.name ?*/_sz; i ++) {
                            free((* /*? p.name ?*/)[i]);
                        }
                    /*- endif -*/
                    free(* /*? p.name ?*/);
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*- if p.direction == 'inout' -*/
                    free(* /*? p.name ?*/);
                /*- endif -*/
            /*- endif -*/

            /*- if p.array -*/
                /*- if p.type == 'string' -*/
                    /*? offset ?*/ = UNMARSHAL_STRING_ARRAY_PARAM(/*? p.name ?*/, /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
                /*- else -*/
                    /*? offset ?*/ = UNMARSHAL_ARRAY_PARAM(/*? p.name ?*/, /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*? offset ?*/ = UNMARSHAL_STRING_PARAM(/*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
            /*- else -*/
                /*? offset ?*/ = UNMARSHAL_PARAM(/*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
            /*- endif -*/
        /*- endfor -*/

        /*- if not allow_trailing_data -*/
        /* Error if there is still payload that hasn't been processed */
        ERR_IF_MALFORMED_RPC_EXCESS_PAYLOAD(/*? size ?*/, /*? offset ?*/, "/*? name ?*/", ({
            goto cleanup_/*? len(output_parameters) ?*/;
        }));
    /*- endif -*/

    return 0;

    /*- for index, q in enumerate(output_parameters) | reverse -*/
cleanup_/*? index + 1 ?*/:
        /*- if q.array -*/
            /*- if q.type == 'string' -*/
                for (int i = 0; i < * /*? q.name ?*/_sz; i++) {
                    free((* /*? q.name ?*/)[i]);
                }
            /*- endif -*/
            free(* /*? q.name ?*/);
        /*- elif q.type == 'string' -*/
            free(* /*? q.name ?*/);
        /*- endif -*/
    /*- endfor -*/
cleanup_0:
            /*-- if return_type == 'string' -*/
                free(* /*? ret ?*/);
            /*-- endif -*/
            return -1;
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

/*# Generates code for marshalling out parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     methods_len: Total number of methods in this interface
  #     input_parameters: All input parameters to this method
  #     allow_trailing_data: Whether to ignore checks for remaining bytes after a message
  #*/
/*- macro make_unmarshal_input_symbols(name, function, buffer, methods_len, input_parameters, allow_trailing_data) -*/
    /*# Validate the types of our arguments #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(methods_len, six.integer_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    static int /*? function ?*/(
    /*- set size = c_symbol('size') -*/
    unsigned /*? size ?*/
    /*- if len(input_parameters) > 0 -*/
        ,
    /*- endif -*/
    /*? show_output_parameter_list(input_parameters) ?*/
    ) {

        /*- set offset = c_symbol('offset') -*/
        unsigned /*? offset ?*/ UNUSED = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if methods_len > 1 -*/
            /* Step over the method index. */
            /*? offset ?*/ += sizeof(/*? macros.type_to_fit_integer(methods_len) ?*/);
        /*- endif -*/

        /* Unmarshal input parameters. */
        /*- for index, p in enumerate(input_parameters) -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
            /*- if p.array -*/
                /*- if p.type == 'string' -*/
                    /*? offset ?*/ = UNMARSHAL_STRING_ARRAY_PARAM(/*? p.name ?*/, /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
                /*- else -*/
                    /*? offset ?*/ = UNMARSHAL_ARRAY_PARAM(/*? p.name ?*/, /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*? offset ?*/ = UNMARSHAL_STRING_PARAM(/*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
            /*- else -*/
                /*? offset ?*/ = UNMARSHAL_PARAM(/*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}))
            /*- endif -*/
        /*- endfor -*/

        /*- if not allow_trailing_data -*/
            ERR_IF_MALFORMED_RPC_EXCESS_PAYLOAD(/*? size ?*/, /*? offset ?*/, "/*? name ?*/", ({
                goto cleanup_/*? len(input_parameters) ?*/;
            }));
        /*- endif -*/

        return 0;
        /*-- for index, q in enumerate(input_parameters) | reverse -*/
cleanup_/*? index + 1 ?*/:
            /*-- if q.array -*/
                /*-- if q.type == 'string' -*/
                    /*-- set mcount = c_symbol() -*/
                    for (int /*? mcount ?*/ = 0; /*? mcount ?*/ < * /*? q.name ?*/_sz; /*? mcount ?*/ ++) {
                        free((* /*? q.name ?*/)[/*? mcount ?*/]);
                    }
                /*-- endif -*/
                free(* /*? q.name ?*/);
            /*-- elif q.type == 'string' -*/
                free(* /*? q.name ?*/);
            /*-- endif -*/
        /*-- endfor -*/
cleanup_0:
        return -1;

    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # size: Name of a variable storing the byte length of the message
  # input_parameters: All input parameters to this method
  #*/
/*- macro call_unmarshal_input(function, size, input_parameters) -*/
    /*# Validate our arguments are the expected type #*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    /*? function ?*/(
    /*? size ?*/
    /*- if len(input_parameters) > 0 -*/
        ,
    /*- endif -*/
    /*- for p in input_parameters -*/
        /*- if p.array -*/
            /*? p.name ?*/_sz_ptr,
        /*- endif -*/
        /*? p.name ?*/_ptr
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    )
/*- endmacro -*/

/*# Generates code for marshalling out parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     buffer: Buffer symbol (or expression) to marshal into
  #     size: Length of the buffer; possibly not generation-time constant
  #     output_parameters: All output parameters to this method
  #     return_type: Return type of this interface
  #*/
/*- macro make_marshal_output_symbols(name, function, buffer, size, output_parameters, return_type) -*/
    /*# Validate our arguments are the correct type #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(buffer, six.string_types)) ?*/
    /*? assert(isinstance(size, six.string_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    static unsigned /*? function ?*/(
    /*- set ret = c_symbol('return') -*/
    /*- if return_type is not none -*/
        /*- if return_type == 'string' -*/
            char ** /*? ret ?*/
        /*- else -*/
            const /*? macros.show_type(return_type) ?*/ * /*? ret ?*/
        /*- endif -*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*? show_input_parameter_list(output_parameters, ['out', 'inout']) ?*/
    /*- if return_type is none and len(output_parameters) == 0 -*/
        void
    /*- endif -*/
    ) {

        /*- set offset = c_symbol('offset') -*/
        unsigned /*? offset ?*/ = 0;

        /*- set base = c_symbol('buffer_base') -*/
        void * /*? base ?*/ UNUSED = (void*)(/*? buffer ?*/);

        /*- if return_type is not none -*/
            /* Marshal the return value. */
            /*- if return_type == 'string' -*/
                /*? offset ?*/ = MARSHAL_STRING_PARAM(* /*? ret ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "return value")
            /*- else -*/
                /*? offset ?*/ = MARSHAL_PARAM(/*? ret ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "return value")
            /*- endif -*/
        /*- endif -*/

        /* Marshal output parameters. */
        /*- for p in output_parameters -*/
            /*? assert(isinstance(p.type, six.string_types)) ?*/
            /*- if p.array -*/
                /*- if p.type == 'string' -*/
                    /*? offset ?*/ = MARSHAL_STRING_ARRAY_PARAM((* /*? p.name ?*/), /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
                /*- else -*/
                    /*? offset ?*/ = MARSHAL_ARRAY_PARAM((* /*? p.name ?*/), /*? p.name ?*/_sz, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
                /*- endif -*/
            /*- elif p.type == 'string' -*/
                /*? offset ?*/ = MARSHAL_STRING_PARAM(* /*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
            /*- else -*/
                /*? offset ?*/ = MARSHAL_PARAM(/*? p.name ?*/, /*? base ?*/, /*? size ?*/, /*? offset ?*/, "/*? name ?*/", "/*? p.name ?*/")
            /*- endif -*/
        /*- endfor -*/

        assert(/*? offset ?*/ <= /*? size ?*/ &&
            "uncaught buffer overflow while marshalling outputs for /*? name ?*/");

        return /*? offset ?*/;
    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # output_parameters: All output parameters to this method
  # return_type: Return type of this interface
  # ret_ptr: Pointer for the return value
  #*/
/*- macro call_marshal_output(function, output_parameters, return_type, ret_ptr) -*/
    /*# Validate our arguments are the correct type #*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    /*? function ?*/(
    /*- if return_type is not none -*/
        /*? assert(isinstance(ret_ptr, six.string_types)) ?*/
        /*? ret_ptr ?*/
        /*- if len(output_parameters) > 0 -*/
            ,
        /*- endif -*/
    /*- endif -*/
    /*- for p in output_parameters -*/
        /*- if p.array -*/
            /*? p.name ?*/_sz_ptr,
        /*- endif -*/
        /*? p.name ?*/_ptr
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    )
/*- endmacro -*/
