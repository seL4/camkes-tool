/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <stdio.h>
#include <sel4/sel4.h>
#include <utils/util.h>
#include <bits/syscall.h>
#include <bits/errno.h>
#include <camkes/syscalls.h>
#include <muslcsys/vsyscall.h>

struct {
    int sysno;
    muslcsys_syscall_t syscall;
} syscalls[] = {
    {__NR_set_tid_address, camkes_sys_set_tid_address},
    {__NR_sched_yield, camkes_sys_sched_yield},
    {__NR_exit, camkes_sys_exit},
    {__NR_gettid, camkes_sys_gettid},
    {__NR_getpid, camkes_sys_getpid},
    {__NR_getppid, camkes_sys_getppid},
    {__NR_tgkill, camkes_sys_tgkill},
    {__NR_mlock, camkes_sys_mlock},
    {__NR_munlock, camkes_sys_munlock},
    {__NR_mlockall, camkes_sys_mlockall},
    {__NR_munlockall, camkes_sys_munlockall},
    {__NR_madvise, camkes_sys_madvise},
    {__NR_mincore, camkes_sys_mincore},
#ifdef __NR_pause
    {__NR_pause, camkes_sys_pause},
#endif
    {__NR_clock_gettime, camkes_sys_clock_gettime},
#ifdef __NR__newselect
    {__NR__newselect, camkes_sys__newselect},
#endif
#ifdef __NR_sigcation
    {__NR_sigaction, camkes_sys_sigaction},
#endif
    {__NR_rt_sigaction, camkes_sys_rt_sigaction},
    {__NR_uname, camkes_sys_uname},
#if defined(_BSD_SOURCE) || (defined(_XOPEN_SOURCE) && _XOPEN_SOURCE < 500)
    {__NR_sethostname, camkes_sys_sethostname},
    {__NR_setdomainname, camkes_sys_setdomainname},
#endif
#if !defined(CONFIG_ARCH_IA32)
    {__NR_socket, camkes_sys_socket},
    {__NR_bind, camkes_sys_bind},
    {__NR_connect, camkes_sys_connect},
    {__NR_listen, camkes_sys_listen},
    {__NR_accept, camkes_sys_accept},
    {__NR_setsockopt, camkes_sys_setsockopt},
#endif
    {__NR_tkill, camkes_sys_tkill}
};

void camkes_install_syscalls(void)
{
    int i;
    camkes_install_io_syscalls();
    for (i = 0; i < ARRAY_SIZE(syscalls); i++) {
        muslcsys_install_syscall(syscalls[i].sysno, syscalls[i].syscall);
    }
}
