#
# Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.7.2)

include(${KERNEL_HELPERS_PATH})
include(${PLATSUPPORT_HELPERS})
include(dts)

function(append_flags parent_list)
    math(EXPR limit "${ARGC} - 1")
    set(local_flags "${${parent_list}}")
    foreach(i RANGE 1 ${limit})
        set(list "${ARGV${i}}")
        list(GET list 0 check)
        string(
            REGEX
            REPLACE
                " +"
                ";"
                check
                "${check}"
        )
        if(${check})
            list(GET list 1 when_true)
            list(APPEND local_flags "${when_true}")
        else()
            list(LENGTH list len)
            if(${len} GREATER 2)
                list(GET list 2 when_false)
                list(APPEND local_flags "${when_false}")
            endif()
        endif()
    endforeach()
    set(${parent_list} "${local_flags}" PARENT_SCOPE)
endfunction(append_flags)

macro(set_config_guard)
    set(${ARGV})
    if(CAMKES_CONFIG_DEFAULT_ADVANCED)
        mark_as_advanced(${ARGV0})
    endif()
endmacro()

function(set_camkes_flags_from_config list)

    set_config_guard(
        CAmkESVerbose
        OFF
        CACHE
        BOOL
        "Enable verbose output from CAmkES. This is disabled by default as it
        can result in a lot of output, but is useful for debugging CAmkES problems"
    )

    set(local_flags "${${list}}")
    append_flags(local_flags "CAmkESVerbose;--debug")
    set(${list} "${local_flags}" PARENT_SCOPE)
endfunction(set_camkes_flags_from_config)

function(set_camkes_parser_flags_from_config list)

    # These options are not declared with the config_* system because they only
    # need to exist in the build system, and not appear in a configuration
    # library
    set_config_guard(
        CAmkESCPP
        ON
        CACHE
        BOOL
        "Run CPP on the input specification(s) before parsing them into an AST.
        This can allow you to write parameterised specs in the case of more
        complex system"
    )
    set_config_guard(
        CAmkESAllowForwardReferences
        OFF
        CACHE
        BOOL
        "By default, you can only refer to objects in your specification which
        have been defined before the point at which you reference them.
        Selecting this option allows you to also reference objects that are
        defined below the point at which the reference occurs. This option is
        off by default because it leads to a slight performance degradation in
        parsing specification"
    )
    set(local_flags "${${list}}")
    append_flags(
        local_flags "CAmkESAllowForwardReferences;--allow-forward-references"
        "CAmkESCPP;--cpp;--nocpp"
    )
    if(CAmkESCPP)
        find_program(C_PREPROCESSOR cpp)
        if("${C_PREPROCESSOR}" STREQUAL "C_PREPROCESSOR-NOTFOUND")
            message(FATAL_ERROR "Could not find cpp. Override with -DC_PREPROCESSOR=path/to/cpp")
        endif()
        mark_as_advanced(C_PREPROCESSOR)
        list(APPEND local_flags --cpp-bin "${C_PREPROCESSOR}")
    endif()
    set(${list} "${local_flags}" PARENT_SCOPE)

endfunction(set_camkes_parser_flags_from_config)

function(set_camkes_render_flags_from_config list)

    set_config_guard(
        CAmkESDefaultStackSize
        16384
        CACHE
        STRING
        "Stack size to allocate per-component, in bytes. Note that this value
        should be page-aligned. If not, it will be rounded up."
    )

    set_config_guard(
        CAmkESProvideTCBCaps
        ON
        CACHE
        BOOL
        "Hand out TCB caps to components. These caps are used by the component
        to exit cleanly by suspending. Disabling this option leaves components
        with an empty slot in place of their TCB cap. This means they will cap
        fault when attempting to exit. The advantage is that your resulting
        CapDL specification contains no TCB caps and is thus easier to reason
        about."
    )

    set_config_guard(
        CAmkESDefaultPriority
        254
        CACHE
        STRING
        "Default priority for component threads if this is not overridden via an
        attribute. Generally you want to set this as high as possible.
        Defaults to one less than the max priority to avoid interleaving with
        the CapDL intialiser."
    )
    if((${CAmkESDefaultPriority} LESS 0) OR (${CAmkESDefaultPriority} GREATER 255))
        message(FATAL_ERROR "CAmkESDefaultPriority must be [0, 255]")
    endif()

    set_config_guard(
        CAmkESDefaultAffinity
        0
        CACHE
        STRING
        # Default to 0 as this is the index assigned to the BSP (Boot Strap
        # Processor) by seL4
        "Default affinity for component threads if this is not overridden via an
        attribute. Think carefully when organizing your applications for
        multiprocessor operation"
    )
    math(EXPR MaxNumNodesMin1 "${KernelMaxNumNodes} - 1")
    if((${CAmkESDefaultAffinity} < 0) OR (${CAmkESDefaultAffinity} GREATER ${MaxNumNodesMin1}))
        message(FATAL_ERROR "Invalid CAmkESDefaultAffinity")
    endif()

    set_config_guard(
        CAmkESRPCLockElision
        ON
        CACHE
        BOOL
        "Detect when it is safe to exclude locking operations in the seL4RPC
        connector and automatically do so. This is an optimisation that can
        improve the performance of this connector."
    )

    set_config_guard(
        CAmkESLargeFramePromotion
        ON
        CACHE
        BOOL
        "Some hardware platforms support multiple page sizes. In components with
        large virtual address spaces, it is possible to reduce memory usage
        (and consequent load time) by backing the component's address space with
        pages of these larger sizes. When this setting is enabled, small
        consecutive page mappings will be promoted to fewer consecutive large
        mappings. Note that larger frame sizes are directly mapped into page
        directories and can also save the overhead of an accompanying page
        table."
    )

    set_config_guard(
        CAmkESDMALargeFramePromotion
        OFF
        CACHE
        BOOL
        "For components with a configured DMA pool, the frames backing this
        are not automatically promoted to large frames even if the pool is
        sufficiently large. Select this option to enable such promotion
        automatically. This is off by default because it requires support
        for large alignments in your toolchain's assembler, which is often
        absent in ARM toolchains."
    )

    set_config_guard(
        CAmkESFaultHandlers
        ON
        CACHE
        BOOL
        "When a component references invalid virtual memory or an invalid
        capability, the access generates a fault. With this option selected
        a handler is provided that decodes this fault for debugging
        purposes. You will want to disable this in a production system or in
        a system where you want to handle your own faults."
    )

    set(local_flags "${${list}}")

    list(
        APPEND
            local_flags
            --architecture
            ${KernelSel4Arch}
            --default-priority
            ${CAmkESDefaultPriority}
            --default-affinity
            ${CAmkESDefaultAffinity}
            --default-stack-size
            ${CAmkESDefaultStackSize}
    )
    append_flags(
        local_flags
        "KernelIsMCS;--realtime"
        "CAmkESRPCLockElision;--frpc-lock-elision;--fno-rpc-lock-elision"
        "CAmkESProvideTCBCaps;--fprovide-tcb-caps;--fno-provide-tcb-caps"
        "CAmkESLargeFramePromotion;--largeframe"
        "CAmkESDMALargeFramePromotion;--largeframe-dma"
        "CAmkESFaultHandlers;--debug-fault-handlers"
    )

    set(${list} "${local_flags}" PARENT_SCOPE)

endfunction(set_camkes_render_flags_from_config)

set_config_guard(
    CAmkESDTS
    OFF
    CACHE
    BOOL
    "Support using a device tree (.dts) file, which camkes can query
    for device properties. A file path can be provided by as an argument
    to DeclareCAmkESRootserver as DTS_FILE_PATH, otherwise the a dts file
    matching the platform will be found in seL4/tools."
)

set_config_guard(
    CAmkESCapDLVerification
    OFF
    CACHE
    BOOL
    "Generate Isabelle definitions and proofs for CapDL refinement. This
    verifies that the system's capability distribution conforms to the expected
    integrity policy of the component assembly."
)

set_config_guard(
    CAmkESCapDLStaticAlloc
    OFF
    CACHE
    BOOL
    "Statically allocate all capDL objects. This requires the target
     platform to have a DTS file, and also requires a certain amount of
     cooperation from kernel boot (currently available on ARM)."
)

if((NOT CAmkESCapDLStaticAlloc) AND CAmkESCapDLVerification)
    message(FATAL_ERROR "CAmkESCapDLVerification requires CAmkESCapDLStaticAlloc to be enabled")
endif()

# Check static allocation options. These should have been propagated correctly
# by settings.cmake
if(CAmkESCapDLStaticAlloc)
    if(NOT CapDLLoaderStaticAlloc)
        message(FATAL_ERROR "CAmkESCapDLStaticAlloc requires CapDLLoaderStaticAlloc to be enabled")
    endif()
    if(NOT ElfloaderRootserversLast)
        message(
            FATAL_ERROR "CAmkESCapDLStaticAlloc requires ElfloaderRootserversLast to be enabled"
        )
    endif()
endif()

# This also provides PYTHON_CAPDL_PATH
list(APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/projects/capdl)
find_package(capdl REQUIRED)
CapDLToolInstall(install_capdl_tool CAPDL_TOOL_BINARY)

RequireFile(TLS_LINKER_LDS tls.lds PATHS "${CMAKE_CURRENT_LIST_DIR}/libsel4camkes/src")

# Use the camkes script to determine the location of other things
set(CAMKES_TOOL_DIR "${CMAKE_CURRENT_LIST_DIR}")
set(CAMKES_TOOL_BUILTIN_DIR "${CAMKES_TOOL_DIR}/include/builtin")

# Build the environment expected by camkes
set(CAMKES_TOOL_ENVIRONMENT "PYTHONPATH=${CAMKES_TOOL_DIR}:${PYTHON_CAPDL_PATH}")

# Save camkes tool commands
set(CAMKES_PYTHON_COMMAND ${CMAKE_COMMAND} -E env "${CAMKES_TOOL_ENVIRONMENT}" ${PYTHON3})
set(CAMKES_TOOL ${CAMKES_PYTHON_COMMAND} -m camkes.runner)
set(CAMKES_PARSER_TOOL ${CAMKES_PYTHON_COMMAND} -m camkes.parser)
set(
    CAPDL_LINKER
    ${CMAKE_COMMAND}
    -E
    env
    "PYTHONPATH=${PYTHON_CAPDL_PATH}"
    ${PYTHON3}
    ${PYTHON_CAPDL_PATH}/../cdl_utils/capdl_linker.py
)
set(CAPDL_LINKER_DEPENDENCIES "${PYTHON_CAPDL_PATH}/../cdl_utils/capdl_linker.py")
set(
    CAPDL_UNTYPED_GEN
    ${CMAKE_COMMAND}
    -E
    env
    "PYTHONPATH=${PYTHON_CAPDL_PATH}"
    ${PYTHON3}
    ${PYTHON_CAPDL_PATH}/../cdl_utils/untyped_gen.py
)
set(CAPDL_UNTYPED_GEN_DEPENDENCIES "${PYTHON_CAPDL_PATH}/../cdl_utils/untyped_gen.py")

# Search for a FMT tool for reformatting generated CAmkES C files
find_program(CLANG_FORMAT_TOOL clang-format)
if("${CLANG_FORMAT_TOOL}" STREQUAL "CLANG_FORMAT_TOOL-NOTFOUND")
    set(CAMKES_C_FMT_INVOCATION "")
else()
    set(CAMKES_C_FMT_INVOCATION "${CLANG_FORMAT_TOOL} --style=LLVM")
    mark_as_advanced(CLANG_FORMAT_TOOL)
endif()

# Find the sponge tool, or emulate it
find_program(SPONGE_TOOL sponge)
if("${SPONGE_TOOL}" STREQUAL "SPONGE_TOOL-NOTFOUND")
    set(CAMKES_SPONGE_INVOCATION "sh ${CMAKE_CURRENT_BINARY_DIR}/sponge_emul.sh")
    file(
        WRITE
            "${CMAKE_CURRENT_BINARY_DIR}/sponge_emul.sh"
            "python -c 'import sys; data = sys.stdin.read(); f = open(sys.argv[1], \"w\"); f.write(data); f.close()' $@"
    )
else()
    set(CAMKES_SPONGE_INVOCATION "${SPONGE_TOOL}")
    mark_as_advanced(SPONGE_TOOL)
endif()

# Find the Isabelle theory pre-process for formatting theory files
find_program(TPP_TOOL tpp PATHS ${CMAKE_CURRENT_LIST_DIR}/tools)
if("${TPP_TOOL}" STREQUAL "TPP_TOOL-NOTFOUND")
    message(FATAL_ERROR "Failed to find tpp tool")
endif()
mark_as_advanced(TPP_TOOL)

file(
    GLOB
        CAMKES_TOOL_FILES
        ${CMAKE_CURRENT_LIST_DIR}/camkes/ast/*.py
        ${CMAKE_CURRENT_LIST_DIR}/camkes/internal/*.py
        ${CMAKE_CURRENT_LIST_DIR}/camkes/parser/*.py
        ${CMAKE_CURRENT_LIST_DIR}/camkes/runner/*.py
        ${CMAKE_CURRENT_LIST_DIR}/camkes/templates/Template.py
        ${CMAKE_CURRENT_LIST_DIR}/camkes/templates/macros.py
)

file(GLOB PYTHON_CAPDL_FILES ${PYTHON_CAPDL_PATH}/capdl/*.py)

# CAmkES defines its own heaps and for this to work muslcsys must not be
# configured to use a static morecore. We make the morecore dynamic by setting
# the size to 0
set(LibSel4MuslcSysMorecoreBytes 0 CACHE STRING "" FORCE)

# This is called from the context of a CAmkES application that has decided what
# the 'root' application is. This function will effectively generate a rule for
# building the final rootserver image
function(DeclareCAmkESRootserver adl)
    cmake_parse_arguments(
        PARSE_ARGV
        1
        CAMKES_ROOT
        "" # Option arguments
        "DTS_FILE_PATH" # Single arguments
        "CPP_FLAGS;CPP_INCLUDES" # Multiple arguments
    )

    # Stash this request as a global property. The main CAmkES build file will
    # call GenerateCAmkESRootserver later once all the build scripts are
    # processed
    get_property(declared GLOBAL PROPERTY CAMKES_ROOT_DECLARED)
    if(declared)
        message(FATAL_ERROR "A CAmkES rootserver was already declared")
    endif()
    foreach(include IN LISTS CAMKES_ROOT_CPP_INCLUDES)
        get_absolute_list_source_or_binary(include "${include}")
        list(APPEND CAMKES_ROOT_CPP_FLAGS "-I${include}")
    endforeach()
    # this define can be used to detect if the CAmkES Tool is processing a file
    # or the C compiler. This allows excluding C specific things from CAmkES in
    # shared header files.
    list(APPEND CAMKES_ROOT_CPP_FLAGS "-DCAMKES_TOOL_PROCESSING")
    get_absolute_list_source_or_binary(adl "${adl}")
    set_property(GLOBAL PROPERTY CAMKES_ROOT_ADL "${adl}")
    set_property(GLOBAL PROPERTY CAMKES_ROOT_CPP_FLAGS "${CAMKES_ROOT_CPP_FLAGS}" APPEND)
    set_property(GLOBAL PROPERTY CAMKES_ROOT_DECLARED TRUE)
    if(
        ${CAmkESDTS}
        AND
            NOT
            "${CAMKES_ROOT_DTS_FILE}"
            STREQUAL
            ""
    )
        get_absolute_list_source_or_binary(CAMKES_ROOT_DTS_FILE_PATH "${CAMKES_ROOT_DTS_FILE_PATH}")
    endif()
    set_property(GLOBAL PROPERTY CAMKES_ROOT_DTB_FILE_PATH "${CAMKES_ROOT_DTB_FILE_PATH}")
    set_property(GLOBAL PROPERTY CAMKES_ROOT_DTS_FILE_PATH "${CAMKES_ROOT_DTS_FILE_PATH}")
endfunction(DeclareCAmkESRootserver)

# Called to actually generate the definitions for the CAmkES rootserver. Due to
# its use of properties for some configuration it needs to be run after all
# other build scripts, typically by the main CAmkES build file
function(GenerateCAmkESRootserver)
    # Retrieve properties from the declare call above
    get_property(declared GLOBAL PROPERTY CAMKES_ROOT_DECLARED)
    if(NOT declared)
        message(FATAL_ERROR "No CAmkES rootserver was declared")
    endif()
    get_property(adl GLOBAL PROPERTY CAMKES_ROOT_ADL)
    get_property(CAMKES_ROOT_CPP_FLAGS GLOBAL PROPERTY CAMKES_ROOT_CPP_FLAGS)
    get_property(dts_file GLOBAL PROPERTY CAMKES_ROOT_DTS_FILE_PATH)
    get_property(dtb_file GLOBAL PROPERTY CAMKES_ROOT_DTB_FILE_PATH)
    set(CAMKES_TOOL_DEPENDENCIES "")
    get_filename_component(CAMKES_CDL_TARGET "${adl}" NAME_WE)
    set(CAMKES_CDL_TARGET "${CMAKE_CURRENT_BINARY_DIR}/${CAMKES_CDL_TARGET}.cdl")
    # Get an absolute reference to the ADL source
    get_absolute_list_source_or_binary(CAMKES_ADL_SOURCE "${adl}")
    # Declare a common CAMKES_FLAGS that we will need to give to every
    # invocation of camkes
    set(CAMKES_PARSER_FLAGS "--import-path=${CAMKES_TOOL_BUILTIN_DIR}")

    if(${CAmkESDTS})
        if(NOT EXISTS "${dtb_file}")
            # Find the dts to use
            if("${dts_file}" STREQUAL "")
                # use the kernel's generated DTB file
                set(dtb_file ${KernelDTBPath})
            elseif(NOT EXISTS "${dts_file}")
                message(FATAL_ERROR "Could not find dts file ${dts_file}")
            else()
                # generate a DTB file from the path provided
                GenDTB("${dts_file}" dtb_file)
            endif()
        endif()
        list(APPEND CAMKES_PARSER_FLAGS "--dtb=${dtb_file}")
    endif()

    # Grab the list of GPIO pins for the parser
    if(NOT ${KernelPlatform} STREQUAL "pc99")
        if(NOT ${KernelARMPlatform} STREQUAL "")
            get_device_list(gpio_list gpio ${KernelARMPlatform})
        else()
            get_device_list(gpio_list gpio ${KernelPlatform})
        endif()
        if(EXISTS ${gpio_list})
            list(APPEND CAMKES_PARSER_FLAGS "--gpio-list=${gpio_list}")
        endif()
    endif()

    set_camkes_flags_from_config(CAMKES_FLAGS)
    set_camkes_parser_flags_from_config(CAMKES_PARSER_FLAGS)
    set_camkes_render_flags_from_config(CAMKES_RENDER_FLAGS)

    foreach(flag IN LISTS CAMKES_ROOT_CPP_FLAGS)
        if(NOT "--cpp" IN_LIST CAMKES_PARSER_FLAGS)
            message(
                FATAL_ERROR "Given CPP_FLAGS ${CAMKES_ROOT_CPP_FLAGS} but CAmkESCPP is disabled"
            )
        endif()
        list(APPEND CAMKES_PARSER_FLAGS "--cpp-flag=${flag}")
    endforeach()
    # Retrieve any extra import paths
    get_property(imports GLOBAL PROPERTY CAmkESExtraImportPaths)
    foreach(import IN LISTS imports)
        list(APPEND CAMKES_PARSER_FLAGS "--import-path=${import}")
    endforeach()
    # Retrieve any template paths
    get_property(templates GLOBAL PROPERTY CAmkESTemplatePaths)
    foreach(template IN LISTS templates)
        list(APPEND CAMKES_RENDER_FLAGS --templates "${template}")
    endforeach()

    set(CAMKES_AST_PICKLE "${CMAKE_CURRENT_BINARY_DIR}/ast.pickle")
    set(CAMKES_AST_DEP_FILE "${CAMKES_AST_PICKLE}.d")
    execute_process_with_stale_check(
        "${CAMKES_AST_PICKLE}.cmd"
        "${CAMKES_AST_DEP_FILE}"
        "${CAMKES_AST_PICKLE}"
        "${CAMKES_TOOL_FILES} ${PYTHON_CAPDL_FILES}"
        COMMAND
        ${CAMKES_PARSER_TOOL}
        ${CAMKES_FLAGS}
        ${CAMKES_PARSER_FLAGS}
        --makefile-dependencies
        "${CAMKES_AST_DEP_FILE}"
        --file
        "${CAMKES_ADL_SOURCE}"
        --save-ast
        "${CAMKES_AST_PICKLE}"
        WORKING_DIRECTORY
        "${CMAKE_CURRENT_BINARY_DIR}"
        INPUT_FILE
        /dev/stdin
        OUTPUT_FILE
        /dev/stdout
        ERROR_FILE
        /dev/stderr
        RESULT_VARIABLE
        camkes_gen_error
    )
    if(camkes_gen_error)
        file(REMOVE ${CAMKES_AST_PICKLE})
        message(FATAL_ERROR "Failed to generate ${CAMKES_AST_PICKLE}")
    endif()

    set(CAMKES_CMAKE_FILE "${CMAKE_CURRENT_BINARY_DIR}/camkes-gen.cmake")
    set(CAMKES_CMAKE_DEP_FILE "${CAMKES_CMAKE_FILE}.d")
    execute_process_with_stale_check(
        "${CAMKES_CMAKE_FILE}.cmd"
        "${CAMKES_CMAKE_DEP_FILE}"
        "${CAMKES_CMAKE_FILE}"
        "${CAMKES_TOOL_FILES} ${PYTHON_CAPDL_FILES} ${CAMKES_AST_PICKLE}"
        COMMAND
        ${CAMKES_TOOL}
        ${CAMKES_FLAGS}
        ${CAMKES_RENDER_FLAGS}
        --makefile-dependencies
        "${CAMKES_CMAKE_DEP_FILE}"
        --load-ast
        "${CAMKES_AST_PICKLE}"
        --item
        assembly/
        --template
        camkes-gen.cmake
        --outfile
        "${CAMKES_CMAKE_FILE}"
        WORKING_DIRECTORY
        "${CMAKE_CURRENT_BINARY_DIR}"
        INPUT_FILE
        /dev/stdin
        OUTPUT_FILE
        /dev/stdout
        ERROR_FILE
        /dev/stderr
        RESULT_VARIABLE
        camkes_gen_error
    )
    if(camkes_gen_error)
        file(REMOVE ${CAMKES_CMAKE_FILE})
        message(FATAL_ERROR "Failed to generate ${CAMKES_CMAKE_FILE}")
    endif()

    # We set a property to indicate that we have done execute_process (which
    # happens during the generation phase. This just allows us to do some
    # debugging and detect cases where options are changed *after* this point
    # that would have affected the execute_process
    set_property(GLOBAL PROPERTY CAMKES_GEN_DONE TRUE)
    include("${CAMKES_CMAKE_FILE}")

endfunction(GenerateCAmkESRootserver)

# Internal helper function for setting camkes component properties
# The following common parameters are supported
#
#   SOURCES <src1> <src2> ...
#   INCLUDES <inc1> <inc2> ...
#   C_FLAGS <flag1> <flag2> ...
#   LD_FLAGS <flag1> <flag2> ...
#   LIBS <lib1> <lib1> ...
#
# For CakeML components, these parameters are supported
#
#   CAKEML_HEAP_SIZE <val>
#       sets target propery COMPONENT_CAKEML_HEAP_SIZE
#
#   CAKEML_STACK_SIZE <val>
#       sets target propery COMPONENT_CAKEML_STACK_SIZE
#
#   CAKEML_SOURCES <src1> <src2> ...
#   CAKEML_DEPENDS <dep1> <dep2> ...
#   CAKEML_INCLUDES<inc1> <inc2> ...
#
#   LINKER_LANGUAGE <lng>
#       sets target propery COMPONENT_LINKER_LANGUAGE
#
#   TEMPLATE_SOURCES
#   TEMPLATE_HEADERS
#
function(AppendCAmkESComponentTarget target_name)
    cmake_parse_arguments(
        PARSE_ARGV
        1
        CAMKES_COMPONENT
        "" # Option arguments
        "CAKEML_HEAP_SIZE;CAKEML_STACK_SIZE;LINKER_LANGUAGE" # Single arguments
        "SOURCES;CAKEML_SOURCES;CAKEML_DEPENDS;CAKEML_INCLUDES;INCLUDES;C_FLAGS;LD_FLAGS;LIBS;TEMPLATE_SOURCES;TEMPLATE_HEADERS" # Multiple aguments
    )
    # Declare a target that we will set properties on
    if(NOT (TARGET "${target_name}"))
        add_custom_target("${target_name}")
    endif()
    # Get absolute paths for the includes and sources
    set(includes "")
    set(sources "")
    set(cakeml_sources "")
    set(cakeml_includes "")
    foreach(inc IN LISTS CAMKES_COMPONENT_INCLUDES)
        get_absolute_list_source_or_binary(inc "${inc}")
        list(APPEND includes "${inc}")
    endforeach()
    foreach(file IN LISTS CAMKES_COMPONENT_SOURCES)
        get_absolute_list_source_or_binary(file "${file}")
        list(APPEND sources "${file}")
    endforeach()
    foreach(file IN LISTS CAMKES_COMPONENT_CAKEML_SOURCES)
        get_absolute_list_source_or_binary(file "${file}")
        list(APPEND cakeml_sources "${file}")
    endforeach()
    foreach(file IN LISTS CAMKES_COMPONENT_CAKEML_INCLUDES)
        get_absolute_list_source_or_binary(file "${file}")
        list(APPEND cakeml_includes "${file}")
    endforeach()
    set_property(TARGET "${target_name}" APPEND PROPERTY COMPONENT_INCLUDES "${includes}")
    set_property(TARGET "${target_name}" APPEND PROPERTY COMPONENT_SOURCES "${sources}")
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_TEMPLATE_SOURCES "${CAMKES_COMPONENT_TEMPLATE_SOURCES}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_TEMPLATE_HEADERS "${CAMKES_COMPONENT_TEMPLATE_HEADERS}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_CAKEML_SOURCES "${cakeml_sources}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_CAKEML_INCLUDES "${cakeml_includes}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_CAKEML_DEPENDS "${CAMKES_COMPONENT_CAKEML_DEPENDS}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_C_FLAGS "${CAMKES_COMPONENT_C_FLAGS}"
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY COMPONENT_LD_FLAGS "${CAMKES_COMPONENT_LD_FLAGS}"
    )
    set_property(TARGET "${target_name}" APPEND PROPERTY COMPONENT_LIBS "${CAMKES_COMPONENT_LIBS}")
    # Overwrite any previous CakeML heap or stack size
    if(CAMKES_COMPONENT_CAKEML_HEAP_SIZE)
        set_property(
            TARGET "${target_name}"
            PROPERTY COMPONENT_CAKEML_HEAP_SIZE "${CAMKES_COMPONENT_CAKEML_HEAP_SIZE}"
        )
    endif()
    if(CAMKES_COMPONENT_CAKEML_STACK_SIZE)
        set_property(
            TARGET "${target_name}"
            PROPERTY COMPONENT_CAKEML_STACK_SIZE "${CAMKES_COMPONENT_CAKEML_STACK_SIZE}"
        )
    endif()
    if(CAMKES_COMPONENT_LINKER_LANGUAGE)
        set_property(
            TARGET "${target_name}"
            APPEND
            PROPERTY COMPONENT_LINKER_LANGUAGE "${CAMKES_COMPONENT_LINKER_LANGUAGE}"
        )
    endif()
endfunction(AppendCAmkESComponentTarget)

# Internal helper function for setting camkes component properties
function(DeclareCAmkESConnector name)
    set(target_name CAmkESConnector_${name})
    cmake_parse_arguments(
        PARSE_ARGV
        1
        CAMKES_CONNECTOR
        "" # Option arguments
        "FROM;TO;CAKEML_TO;FROM_HEADER;TO_HEADER" # Single arguments
        "FROM_LIBS;TO_LIBS" # Multiple aguments
    )
    # Declare a target that we will set properties on
    if(NOT (TARGET "${target_name}"))
        add_custom_target("${target_name}")
    endif()
    set_property(TARGET "${target_name}" APPEND PROPERTY CONNECTOR_FROM ${CAMKES_CONNECTOR_FROM})
    set_property(TARGET "${target_name}" APPEND PROPERTY CONNECTOR_TO ${CAMKES_CONNECTOR_TO})
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY CONNECTOR_FROM_HEADER ${CAMKES_CONNECTOR_FROM_HEADER}
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY CONNECTOR_FROM_LIBS ${CAMKES_CONNECTOR_FROM_LIBS}
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY CONNECTOR_TO_HEADER ${CAMKES_CONNECTOR_TO_HEADER}
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY CONNECTOR_TO_LIBS ${CAMKES_CONNECTOR_TO_LIBS}
    )
    set_property(
        TARGET "${target_name}"
        APPEND
        PROPERTY CONNECTOR_CAKEML_TO ${CAMKES_CONNECTOR_CAKEML_TO}
    )
endfunction(DeclareCAmkESConnector)

# This is called by CAmkES components to declare information needed for the
# camkes-gen.cmake to actually build them. Can be called multiple times to
# append additional information.
function(DeclareCAmkESComponent name)
    AppendCAmkESComponentTarget(CAmkESComponent_${name} ${ARGN})
endfunction(DeclareCAmkESComponent)

# Declare built-in components that are constructed from templates and have no
# source files
DeclareCAmkESComponent(debug_server)
DeclareCAmkESComponent(debug_serial)

# Extend a particular instantiation of a CAmkES component with additional
# information. This takes similar arguments to DeclareCAmkESComponent and all
# of the declared includes, flags etc also apply to the sources from
# DeclareCAmkESComponent. The includes provided here will be passed prior to
# the original includes allowing for overriding. This can be called multiple
# times for the same instance to repeatedly extend it. Similar flags will be
# placed after.
function(ExtendCAmkESComponentInstance component_name instance_name)
    AppendCAmkESComponentTarget(CAmkESComponent_${component_name}_instance_${instance_name} ${ARGN})
endfunction(ExtendCAmkESComponentInstance)

# Helper function for adding additional import paths. Largely it exists to
# allow list files to give relative paths and have them automatically expanded
# to absolute paths We add the import paths to a property, instead of a target,
# since we need to use it in an `execute_process` above, which cannot take
# generator expressions
function(CAmkESAddImportPath)
    # Ensure we haven't generated the camkes-gen.cmake yet
    get_property(is_done GLOBAL PROPERTY CAMKES_GEN_DONE)
    if(is_done)
        message(FATAL_ERROR "Adding import path after camkes-gen.cmake has been generated")
    endif()
    foreach(arg IN LISTS ARGV)
        get_absolute_list_source_or_binary(arg "${arg}")
        set_property(GLOBAL APPEND PROPERTY CAmkESExtraImportPaths "${arg}")
    endforeach()
endfunction(CAmkESAddImportPath)

# Add an import path but only if it exists
function(CAmkESMaybeAddImportPath)
    foreach(arg IN LISTS ARGV)
        if(EXISTS ${arg})
            CAmkESAddImportPath(${arg})
        endif()
    endforeach()
endfunction()

function(CAmkESAddTemplatesPath)
    # Ensure we haven't generated the camkes-gen.cmake yet
    get_property(is_done GLOBAL PROPERTY CAMKES_GEN_DONE)
    if(is_done)
        message(FATAL_ERROR "Adding templates path after camkes-gen.cmake has been generated")
    endif()
    foreach(arg IN LISTS ARGV)
        get_absolute_list_source_or_binary(arg "${arg}")
        set_property(GLOBAL APPEND PROPERTY CAmkESTemplatePaths "${arg}")
    endforeach()
endfunction(CAmkESAddTemplatesPath)

include(${CMAKE_CURRENT_LIST_DIR}/components/components.cmake)

# Function to add an include path to the c preprocessor when running over
# camkes ADL files (example.camkes).
function(CAmkESAddCPPInclude)
    foreach(arg IN LISTS ARGV)
        get_absolute_list_source_or_binary(arg "${arg}")
        set_property(GLOBAL APPEND PROPERTY CAMKES_ROOT_CPP_FLAGS "-I${arg}")
    endforeach()
endfunction()

# Declare all built-in templates
include(${CMAKE_CURRENT_LIST_DIR}/camkes/templates/templates.cmake)
