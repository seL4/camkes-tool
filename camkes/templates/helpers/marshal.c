/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*- macro show_input_parameter(p, namespace_prefix='') -*/
    /*- if p.direction == 'in' -*/
        /*-- if p.array --*/
            size_t /*? namespace_prefix ?*//*? p.name ?*/_sz,
            /*- if p.type == 'string' -*/
                char **
            /*- else -*/
                const /*? macros.show_type(p.type) ?*/ *
            /*- endif -*/
        /*-- elif p.type == 'string' --*/
            const char *
        /*- else -*/
            /*?- macros.show_type(p.type) -?*/
        /*- endif -*/ /*? namespace_prefix ?*//*? p.name -?*/
    /*- else -*/
        /*- if p.array -*/
            /*- if p.direction == 'refin' -*/
                const
            /*- endif -*/
            size_t * /*? namespace_prefix ?*//*? p.name ?*/_sz,
            /*- if p.type == 'string' -*/
                char ***
            /*- else -*/
                /*?- macros.show_type(p.type) ?*/ **
            /*- endif -*/
        /*- elif p.type == 'string' -*/
            char **
        /*- else -*/
            /*- if p.direction == 'refin' -*/
                const
            /*- endif -*/
            /*?- macros.show_type(p.type) ?*/ *
        /*- endif -*/
        /*? namespace_prefix ?*//*? p.name ?*/
    /*- endif -*/
/*- endmacro -*/

/*- macro show_input_parameter_list(parameters, valid_directions, namespace_prefix='') -*/
    /*-- for p in parameters --*/
        /*?- assert(p.direction in valid_directions) -?*/
        /*?- show_input_parameter(p, namespace_prefix) ?*//*- if not loop.last -*/,/*- endif -*/
    /*-- endfor --*/
/*- endmacro -*/

/*- macro show_output_parameter(p, namespace_prefix='') -*/
    /*- if p.array -*/
        size_t * /*? namespace_prefix ?*//*? p.name ?*/_sz,
        /*?- macros.show_type(p.type) -?*/ ** /*?- namespace_prefix ?*//*? p.name -?*/
    /*- else -*/
        /*?- macros.show_type(p.type) -?*/ * /*?- namespace_prefix ?*//*? p.name -?*/
    /*- endif -*/
/*- endmacro -*/

/*- macro show_output_parameter_list(parameters, namespace_prefix='') -*/
    /*-- for p in parameters --*/
        /*?- show_output_parameter(p, namespace_prefix) -?*//*-- if not loop.last --*/,/*-- endif --*/
    /*-- endfor --*/
/*- endmacro -*/

/*# Generates code for marshalling input parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     method_index: Index of this method in the containing interface
  #     methods_len: Total number of methods in this interface
  #     input_parameters: All input parameters to this method
  #*/
/*- macro make_marshal_input_symbols(name, function, method_index, methods_len, input_parameters) -*/
    /*# Validate that our arguments are the correct type #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(methods_len, six.integer_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    static unsigned /*? function ?*/(void * base, size_t size
    /*-- if len(input_parameters) > 0 --*/
        ,
    /*-- endif -*/
    /*?- show_input_parameter_list(input_parameters, ['in', 'refin', 'inout'], namespace_prefix="p_") -?*/
    ) {

        unsigned offset = 0;

        /*- if methods_len > 1 -*/
            /* Marshal the method index. */
            /*? macros.type_to_fit_integer(methods_len) ?*/ method_index = /*? method_index ?*/;
            offset = MARSHAL_PARAM(&method_index, base, size, offset, "/*? name ?*/", "method_index");
        /*- endif -*/

        /*- for p in input_parameters -*/
            /*-- if loop.first -*/
                /* Marshal the parameters. */
            /*-- endif -*/
            /*?- assert(isinstance(p.type, six.string_types)) ?*/

            /*#- Construct parameter pointers. We do this here to consolidate where we
             * are taking the address of local variables. In future, we need to avoid
             * doing this for verification.
             #*/
            /*-- set ptr = "p_%s_ptr" % p.name -*/
            /*-- set ptr_sz = "p_%s_ptr_sz" % p.name -*/
            /*-- set ptr_str = "p_%s_ptr_str" % p.name -*/
            /*-- set ptr_arr = "p_%s_ptr_arr" % p.name -*/
            /*-- if p.direction == 'in' -*/
                /*-- if p.array -*/
                    size_t * /*? ptr_sz ?*/ = &p_/*? p.name ?*/_sz;
                    * /*? ptr_sz ?*/ = p_/*? p.name ?*/_sz;
                    /*-- if p.type == 'string' -*/
                        char ** /*? ptr_arr ?*/ = p_/*? p.name ?*/;
                    /*-- else -*/
                        const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = p_/*? p.name ?*/;
                    /*-- endif -*/
                /*-- elif p.type == 'string' -*/
                    const char * /*? ptr_str ?*/ = p_/*? p.name ?*/;
                /*-- else -*/
                    /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = &p_/*? p.name ?*/;
                /*-- endif -*/
            /*-- else -*/
                /*-- if p.array -*/
                    const size_t * /*? ptr_sz ?*/ = p_/*? p.name ?*/_sz;
                    /*-- if p.type == 'string' -*/
                        char ** /*? ptr_arr ?*/ = * p_/*? p.name ?*/;
                    /*-- else -*/
                        const /*? macros.show_type(p.type) ?*/ * /*? ptr_arr ?*/ = * p_/*? p.name ?*/;
                    /*-- endif -*/
                /*-- elif p.type == 'string' -*/
                    const char * /*? ptr_str ?*/ = * p_/*? p.name ?*/;
                /*-- else -*/
                    const /*? macros.show_type(p.type) ?*/ * /*? ptr ?*/ = p_/*? p.name ?*/;
                /*-- endif -*/
            /*-- endif -*/

            /*-- if p.array -*/
                /*-- if p.type == 'string' -*/
                    offset = MARSHAL_STRING_ARRAY_PARAM(/*? ptr_arr ?*/, /*? ptr_sz ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
                /*-- else -*/
                    offset = MARSHAL_ARRAY_PARAM(/*? ptr_arr ?*/, /*? ptr_sz ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
                /*-- endif -*/
            /*-- elif p.type == 'string' -*/
                offset = MARSHAL_STRING_PARAM(/*? ptr_str ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
            /*-- else -*/
                offset = MARSHAL_PARAM(/*? ptr ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
            /*-- endif -*/
        /*- endfor -*/

        assert(offset <= size &&
            "uncaught buffer overflow while marshalling inputs for /*? name ?*/");

        return offset;
    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will marshal input parameters
  # function: Name of function to invoke
  # buffer: Buffer symbol (or expression) to marshal into
  # size: Length of the buffer; possibly not generation-time constant
  # input_parameters: All input parameters to this method
  #*/
/*- macro call_marshal_input(function, buffer, size, input_parameters, namespace_prefix='') -*/
    /*#- Validate our arguments are the correct types #*/
    /*?- assert(isinstance(function, six.string_types)) ?*/
    /*?- assert(isinstance(buffer, six.string_types)) ?*/
    /*?- assert(isinstance(size, (six.string_types,six.integer_types))) ?*/
    /*?- assert(isinstance(input_parameters, (list, tuple))) ?*/

    /*?- function ?*/(/*? buffer ?*/, /*? size ?*/
    /*-- for p in input_parameters --*/,
        /*- if p.array -*//*? namespace_prefix ?*//*? p.name ?*/_sz,/*- endif -*/
        /*?- namespace_prefix ?*//*? p.name ?*/
    /*-- endfor --*/
    )
/*- endmacro -*/


/*# Generates code for marshalling out parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     method_index: Index of this method in the containing interface
  #     output_parameters: All output parameters to this method
  #     return_type: Return type of this interface
  #     allow_trailing_data: Whether to ignore checks for remaining bytes after a message
  #*/
/*# Whether to ignore checks for remaining bytes after a message #*/
/*- macro make_unmarshal_output_symbols(name, function, method_index, output_parameters, return_type, allow_trailing_data) -*/
    /*# Validate our argument types #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(method_index, six.integer_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/
    /*? assert(isinstance(allow_trailing_data, bool)) ?*/

    static int /*? function ?*/(void * base, unsigned size
    /*-- if return_type is not none or len(output_parameters) > 0 --*/
        ,
    /*-- endif -*/
    /*-- if return_type is not none -*/
        /*?- macros.show_type(return_type) ?*/ * return_value
        /*-- if len(output_parameters) > 0 -*/,/*- endif -*/
    /*-- endif -*/
    /*?- show_output_parameter_list(output_parameters, namespace_prefix="p_") ?*/
    ) {

        unsigned offset = 0;

        /*- if return_type is not none -*/
            /* Unmarshal the return value. */
            /*-- if return_type == 'string' -*/
                offset = UNMARSHAL_STRING_PARAM(return_value, base, size, offset, "/*? name ?*/", "return value", ({return -1;}));
            /*-- else -*/
                offset = UNMARSHAL_PARAM(return_value, base, size, offset, "/*? name ?*/", "return value", ({return -1;}));
            /*- endif -*/
        /*- endif -*/

        /*-- for index, p in enumerate(output_parameters) -*/
            /*-- if loop.first -*/
                /* Unmarshal the parameters. */
            /*-- endif -*/
            /*?- assert(isinstance(p.type, six.string_types)) ?*/
            /*-- if p.array -*/
                /*-- if p.direction == 'inout' -*/
                    /*-- if p.type == 'string' -*/
                        /* At this point p_/*? p.name ?*/_sz should still contain the old size */
                        for (int i = 0; i < * p_/*? p.name ?*/_sz; i ++) {
                            free((* p_/*? p.name ?*/)[i]);
                        }
                    /*-- endif -*/
                    free(* p_/*? p.name ?*/);
                /*-- endif -*/
            /*-- elif p.type == 'string' -*/
                /*-- if p.direction == 'inout' -*/
                    free(* p_/*? p.name ?*/);
                /*-- endif -*/
            /*-- endif -*/

            /*-- if p.array -*/
                /*-- if p.type == 'string' -*/
                    offset = UNMARSHAL_STRING_ARRAY_PARAM(p_/*? p.name ?*/, p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
                /*-- else -*/
                    offset = UNMARSHAL_ARRAY_PARAM(p_/*? p.name ?*/, p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
                /*-- endif -*/
            /*-- elif p.type == 'string' -*/
                offset = UNMARSHAL_STRING_PARAM(p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
            /*-- else -*/
                offset = UNMARSHAL_PARAM(p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
            /*-- endif -*/
        /*- endfor -*/

        /*- if not allow_trailing_data -*/
        /* Error if there is still payload that hasn't been processed */
        ERR_IF_MALFORMED_RPC_EXCESS_PAYLOAD(size, offset, "/*? name ?*/", ({
            goto cleanup_/*? len(output_parameters) ?*/;
        }));
    /*- endif -*/

    return 0;

    /*- for index, q in enumerate(output_parameters) | reverse -*/
cleanup_/*? index + 1 ?*/:
        /*- if q.array -*/
            /*- if q.type == 'string' -*/
                for (int i = 0; i < * p_/*? q.name ?*/_sz; i++) {
                    free((* p_/*? q.name ?*/)[i]);
                }
            /*- endif -*/
            free(* p_/*? q.name ?*/);
        /*- elif q.type == 'string' -*/
            free(* p_/*? q.name ?*/);
        /*- endif -*/
    /*- endfor -*/
cleanup_0:
            /*-- if return_type == 'string' -*/
                free(* return_value);
            /*-- endif -*/
            return -1;
    }
/*- endmacro -*/


/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # buffer: Buffer symbol (or expression) to marshal into
  # size: Name of a variable storing the byte length of the message
  # output_parameters: All output parameters to this method
  # return_type: Return type of this interface
  # ret_ptr: Pointer for the return value
  #*/
/*- macro call_unmarshal_output(function, buffer, size, output_parameters, return_type, ret_ptr, namespace_prefix='') -*/
    /*#- Validate the types of our arguments #*/
    /*?- assert(isinstance(function, six.string_types)) ?*/
    /*?- assert(isinstance(buffer, six.string_types)) ?*/
    /*?- assert(isinstance(size, (six.string_types,six.integer_types))) ?*/
    /*?- assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*?- assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    /*?- function ?*/(/*? buffer ?*/,
    /*?- size ?*/
    /*-- if return_type is not none -*/,
        /*?- ret_ptr ?*/
    /*-- endif -*/
    /*-- for p in output_parameters -*/,
    /*-- if p.array -*/
        /*?- namespace_prefix ?*//*? p.name ?*/_sz,
    /*-- endif -*/
    /*?- namespace_prefix ?*//*? p.name ?*/
    /*-- endfor --*/
    )
/*- endmacro -*/

/*# Generates code for marshalling out parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     methods_len: Total number of methods in this interface
  #     input_parameters: All input parameters to this method
  #     allow_trailing_data: Whether to ignore checks for remaining bytes after a message
  #*/
/*- macro make_unmarshal_input_symbols(name, function, methods_len, input_parameters, allow_trailing_data) -*/
    /*# Validate the types of our arguments #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(methods_len, six.integer_types)) ?*/
    /*? assert(isinstance(input_parameters, (list, tuple))) ?*/

    static int /*? function ?*/(void * base, unsigned size
    /*-- if len(input_parameters) > 0 --*/
        ,
    /*-- endif --*/
    /*? show_output_parameter_list(input_parameters, namespace_prefix="p_") -?*/
    ) {

        unsigned offset = 0;

        /*- if methods_len > 1 -*/
            /* Step over the method index. */
            offset += sizeof(/*? macros.type_to_fit_integer(methods_len) ?*/);
        /*- endif -*/

        /*- for index, p in enumerate(input_parameters) -*/
            /*-- if loop.first -*/
                /* Unmarshal input parameters. */
            /*-- endif -*/
            /*?- assert(isinstance(p.type, six.string_types)) ?*/
             /*-- if p.array -*/
                /*-- if p.type == 'string' -*/
                    offset = UNMARSHAL_STRING_ARRAY_PARAM(p_/*? p.name ?*/, p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
                /*-- else -*/
                    offset = UNMARSHAL_ARRAY_PARAM(p_/*? p.name ?*/, p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
                /*-- endif -*/
            /*-- elif p.type == 'string' -*/
                offset = UNMARSHAL_STRING_PARAM(p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
            /*-- else -*/
                offset = UNMARSHAL_PARAM(p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/", ({goto cleanup_/*? index ?*/;}));
            /*-- endif -*/
        /*-- endfor -*/

        /*- if not allow_trailing_data -*/
            ERR_IF_MALFORMED_RPC_EXCESS_PAYLOAD(size, offset, "/*? name ?*/", ({
                goto cleanup_/*? len(input_parameters) ?*/;
            }));
        /*- endif -*/

        return 0;
        /*-- for index, q in enumerate(input_parameters) | reverse -*/
cleanup_/*? index + 1 ?*/:
            /*-- if q.array -*/
                /*-- if q.type == 'string' -*/
                    for (int i = 0; i < * p_/*? q.name ?*/_sz; i ++) {
                        free((* p_/*? q.name ?*/)[i]);
                    }
                /*-- endif -*/
                free(* p_/*? q.name ?*/);
            /*-- elif q.type == 'string' -*/
                free(* p_/*? q.name ?*/);
            /*-- endif -*/
        /*-- endfor -*/
cleanup_0:
        return -1;

    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # buffer: Buffer symbol (or expression) to marshal into
  # size: Name of a variable storing the byte length of the message
  # input_parameters: All input parameters to this method
  #*/
/*- macro call_unmarshal_input(function, buffer, size, input_parameters, namespace_prefix='') -*/
    /*#- Validate our arguments are the expected type #*/
    /*?- assert(isinstance(function, six.string_types)) ?*/
    /*?- assert(isinstance(buffer, six.string_types)) ?*/
    /*?- assert(isinstance(size, (six.string_types,six.integer_types))) ?*/
    /*?- assert(isinstance(input_parameters, (list, tuple))) ?*/

    /*?- function ?*/(/*? buffer ?*/, /*? size ?*/
    /*-- for p in input_parameters -*/,
        /*-- if p.array --*/
            /*? namespace_prefix ?*//*? p.name ?*/_sz_ptr,
        /*-- endif --*/
        /*? namespace_prefix ?*//*? p.name ?*/_ptr
    /*-- endfor --*/
    )
/*- endmacro -*/

/*# Generates code for marshalling out parameters to an RPC invocation
  #     name: Name of this method
  #     function: Name of function to create
  #     output_parameters: All output parameters to this method
  #     return_type: Return type of this interface
  #*/
/*- macro make_marshal_output_symbols(name, function, output_parameters, return_type) -*/
    /*# Validate our arguments are the correct type #*/
    /*? assert(isinstance(name, six.string_types)) ?*/
    /*? assert(isinstance(function, six.string_types)) ?*/
    /*? assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*? assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    static unsigned /*? function ?*/(void * base, unsigned size
    /*-- if return_type is not none -*/,
        /*-- if return_type == 'string' --*/
            char ** return_var
        /*-- else --*/
            const /*? macros.show_type(return_type) ?*/ * return_var
        /*-- endif -*/
    /*-- endif -*/
    /*-- if len(output_parameters) > 0 --*/
        ,
    /*-- endif -*/
    /*?- show_input_parameter_list(output_parameters, ['out', 'inout'], namespace_prefix="p_") ?*/
    ) {

        unsigned offset = 0;

        /*- if return_type is not none -*/
            /* Marshal the return value. */
            /*- if return_type == 'string' -*/
                offset = MARSHAL_STRING_PARAM(* return_var, base, size, offset, "/*? name ?*/", "return value");
            /*- else -*/
                offset = MARSHAL_PARAM(return_var, base, size, offset, "/*? name ?*/", "return value");
            /*- endif -*/
        /*- endif -*/

        /*-- for p in output_parameters -*/
            /*-- if loop.first -*/
                /* Marshal output parameters. */
            /*-- endif -*/
            /*?- assert(isinstance(p.type, six.string_types)) ?*/
            /*-- if p.array -*/
                /*-- if p.type == 'string' -*/
                    offset = MARSHAL_STRING_ARRAY_PARAM((* p_/*? p.name ?*/), p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
                /*-- else -*/
                    offset = MARSHAL_ARRAY_PARAM((* p_/*? p.name ?*/), p_/*? p.name ?*/_sz, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
                /*-- endif -*/
            /*-- elif p.type == 'string' -*/
                offset = MARSHAL_STRING_PARAM(* p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
            /*-- else -*/
                offset = MARSHAL_PARAM(p_/*? p.name ?*/, base, size, offset, "/*? name ?*/", "/*? p.name ?*/");
            /*-- endif -*/
        /*- endfor -*/

        assert(offset <= size &&
            "uncaught buffer overflow while marshalling outputs for /*? name ?*/");

        return offset;
    }
/*- endmacro -*/

/*# Emits a call to the C symbol that will unmarshal output parameters
  # function: Name of function to invoke
  # buffer: Buffer symbol (or expression) to marshal into
  # size: Length of the buffer; possibly not generation-time constant
  # output_parameters: All output parameters to this method
  # return_type: Return type of this interface
  # ret_ptr: Pointer for the return value
  #*/
/*- macro call_marshal_output(function, buffer, size, output_parameters, return_type, ret_ptr, namespace_prefix='') -*/
    /*#- Validate our arguments are the correct type #*/
    /*?- assert(isinstance(function, six.string_types)) ?*/
    /*?- assert(isinstance(buffer, six.string_types)) ?*/
    /*?- assert(isinstance(size, (six.string_types,six.integer_types))) ?*/
    /*?- assert(isinstance(output_parameters, (list, tuple))) ?*/
    /*?- assert(return_type is none or isinstance(return_type, six.string_types)) ?*/

    /*?- function ?*/(/*? buffer ?*/, /*? size ?*/
    /*-- if return_type is not none -*/,
        /*?- assert(isinstance(ret_ptr, six.string_types)) ?*/
        /*?- ret_ptr ?*/
    /*-- endif -*/
    /*-- for p in output_parameters -*/,
        /*-- if p.array -*/
            /*?- namespace_prefix ?*//*? p.name ?*/_sz_ptr,
        /*-- endif -*/
        /*?- namespace_prefix ?*//*? p.name ?*/_ptr
    /*-- endfor --*/
    )
/*- endmacro -*/
