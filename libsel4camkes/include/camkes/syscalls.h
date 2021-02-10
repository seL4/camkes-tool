/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdarg.h>
#include <muslcsys/vsyscall.h>

/* Constructor priority of our install syscall functions */
#define CAMKES_SYSCALL_CONSTRUCTOR_PRIORITY MUSLCSYS_WITH_VSYSCALL_PRIORITY

/* Define the syscall installation functions. camkes_install_syscalls
 * is the base one that will install some syscalls and call the rest
 * of the installation functions */
void camkes_install_syscalls();
void camkes_install_io_syscalls();

/* prototype all the syscalls we implement that will be
 * installed by camkes_install_syscalls */
long camkes_sys_set_tid_address(va_list ap);
long camkes_sys_sched_yield(va_list ap);
long camkes_sys_exit(va_list ap);
long camkes_sys_gettid(va_list ap);
long camkes_sys_getpid(va_list ap);
long camkes_sys_getppid(va_list ap);
long camkes_sys_tgkill(va_list ap);
long camkes_sys_brk(va_list ap);
long camkes_sys_mlock(va_list ap);
long camkes_sys_munlock(va_list ap);
long camkes_sys_mlockall(va_list ap);
long camkes_sys_munlockall(va_list ap);
long camkes_sys_madvise(va_list ap);
long camkes_sys_mincore(va_list ap);
long camkes_sys_pause(va_list ap);
long camkes_sys_clock_gettime(va_list ap);
long camkes_sys__newselect(va_list ap);
long camkes_sys_sigaction(va_list ap);
long camkes_sys_rt_sigaction(va_list ap);
long camkes_sys_uname(va_list ap);
long camkes_sys_sethostname(va_list ap);
long camkes_sys_setdomainname(va_list ap);
long camkes_sys_socket(va_list ap);
long camkes_sys_bind(va_list ap);
long camkes_sys_connect(va_list ap);
long camkes_sys_listen(va_list ap);
long camkes_sys_accept(va_list ap);
long camkes_sys_setsockopt(va_list ap);
long camkes_sys_tkill(va_list ap);
