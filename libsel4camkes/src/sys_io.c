/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <sel4/sel4.h>

#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/uio.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <bits/syscall.h>
#include <muslcsys/vsyscall.h>
#include <muslcsys/io.h>

#include <sel4utils/util.h>

#include "sys_io.h"

static muslcsys_syscall_t original_sys_close = NULL;
static muslcsys_syscall_t original_sys_read = NULL;
static muslcsys_syscall_t original_sys_write = NULL;

int sock_close(int fd) __attribute__((weak));
static long camkes_sys_close(va_list ap)
{
    va_list copy;
    va_copy(copy, ap);
    int fd = va_arg(ap, int);
    if (sock_close && valid_fd(fd)) {
        muslcsys_fd_t *fds =  get_fd_struct(fd);
        if (fds->filetype == FILE_TYPE_SOCKET) {
            sock_close(*(int *)fds->data);
        }
    }
    long ret;
    if (original_sys_close) {
        ret = original_sys_close(copy);
    } else {
        ret = -ENOSYS;
    }
    va_end(copy);
    return ret;
}

int sock_write(int sockfd, int count) __attribute__((weak));
static long camkes_sys_write(va_list ap)
{
    va_list copy;
    va_copy(copy, ap);
    int fd = va_arg(ap, int);
    void *buf = va_arg(ap, void *);
    size_t count = va_arg(ap, size_t);

    if (sock_write && sock_data && valid_fd(fd)) {
        muslcsys_fd_t *fds = get_fd_struct(fd);
        if (fds->filetype == FILE_TYPE_SOCKET) {
            int sockfd = *(int *)fds->data;
            ssize_t size = count > PAGE_SIZE_4K ? PAGE_SIZE_4K : count;
            memcpy((char *)sock_data, buf, size);
            return sock_write(sockfd, size);
        }
    }
    long ret;
    if (original_sys_write) {
        ret = original_sys_write(copy);
    } else {
        // redirect to writev as a last resort
        struct iovec io;
        io.iov_base = buf;
        io.iov_len = count;
        ret = writev(fd, &io, 1);
        // as the syscall implementation we expect to return the error directly and have
        // our caller set errno or not. writev, however, is documented as putting its error
        // code in errno. So if writev returns an error we need to get the error out of errno
        // and return it up, so that it can ultimately get put back into errno
        if (ret == -1) {
            ret = errno;
        }
    }
    va_end(copy);
    return ret;
}

int sock_read(int sockfd, int count) __attribute__((weak));
static long camkes_sys_read(va_list ap)
{
    va_list copy;
    va_copy(copy, ap);
    int fd = va_arg(ap, int);
    void *buf = va_arg(ap, void *);
    size_t count = va_arg(ap, size_t);
    if (sock_read && sock_data && valid_fd(fd)) {
        muslcsys_fd_t *fds = get_fd_struct(fd);
        if (fds->filetype == FILE_TYPE_SOCKET) {
            int sockfd = *(int *)fds->data;
            int size = count > PAGE_SIZE_4K ? PAGE_SIZE_4K : count;
            int ret = sock_read(sockfd, size);
            memcpy(buf, (char *)sock_data, ret);
            return ret;
        }
    }
    long ret;
    if (original_sys_read) {
        ret = original_sys_read(copy);
    } else {
        ret = -ENOSYS;
    }
    va_end(copy);
    return ret;
}

int sock_fcntl(int sockfd, int cmd, int val) __attribute__((weak));
static long UNUSED camkes_sys_fcntl64(va_list ap)
{
    int fd = va_arg(ap, int);
    int cmd = va_arg(ap, int);

    int sockfd;
    muslcsys_fd_t *fdt = get_fd_struct(fd);
    if (fdt->filetype == FILE_TYPE_SOCKET && sock_fcntl) {
        sockfd = *(int *)fdt->data;
        long val = va_arg(ap, long);
        return sock_fcntl(sockfd, cmd, val);
    }

    assert(!"sys_fcntl64 not implemented");
    return -EINVAL;
}

void camkes_install_io_syscalls()
{
    original_sys_close = muslcsys_install_syscall(__NR_close, camkes_sys_close);
    assert(original_sys_close);
    original_sys_read = muslcsys_install_syscall(__NR_read, camkes_sys_read);
    assert(original_sys_read);
    original_sys_write = muslcsys_install_syscall(__NR_write, camkes_sys_write);
#ifdef __NR_fcntl64
    muslcsys_install_syscall(__NR_fcntl64, camkes_sys_fcntl64);
#endif
}
