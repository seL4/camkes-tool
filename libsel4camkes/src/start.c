/*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <stddef.h>
#include <sel4runtime/start.h>
#include <stdint.h>
#include <camkes/init.h>
#include <elf.h>

extern unsigned int _tdata_start[];
extern unsigned int _tdata_end[];
extern unsigned int _tbss_end[];
long sel4_vsyscall(long sysnum, ...);

void camkes_start_control(int thread_id, void *ipc_buffer_ptr) {
	uintptr_t tdata_start = (uintptr_t) &_tdata_start[0];
    uintptr_t tdata_end = (uintptr_t) &_tdata_end[0];
    uintptr_t tbss_end = (uintptr_t) &_tbss_end[0];

    Elf_Phdr tls_header = {
        .p_type   = PT_TLS,
        .p_offset = 0,
        .p_vaddr  = (Elf_Addr) tdata_start,
        .p_paddr  = 0,
        .p_filesz = tdata_end - tdata_start,
        .p_memsz  = tbss_end - tdata_start,
        .p_align = sizeof(long),
    };
	auxv_t auxv[] = {
        {
            .a_type = AT_PHENT,
            .a_un.a_val = sizeof(Elf32_Phdr),
        }, {
            .a_type = AT_PHNUM,
            .a_un.a_val = 1,
        }, {
            .a_type = AT_PHDR,
            .a_un.a_ptr = &tls_header,
        }, {
            .a_type = AT_SYSINFO,
            .a_un.a_ptr = &sel4_vsyscall,
        },{
            .a_type = AT_SEL4_IPC_BUFFER_PTR,
            .a_un.a_ptr = ipc_buffer_ptr,
        },{
            // Null terminating entry
            .a_type = AT_NULL,
            .a_un.a_val = 0
        },
    };

    char const * const envp[] = {
        "seL4=1",
        NULL,
    };

    char const * const argv[] = {
        "camkes",
        (char *)(uintptr_t) thread_id,
        NULL,
    };

    __sel4runtime_start_main(main, ARRAY_LENGTH(argv) - 1, argv, envp, auxv);
}
