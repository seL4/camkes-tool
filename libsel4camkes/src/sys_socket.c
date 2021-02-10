/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <sys/socket.h>
#include <muslcsys/io.h>

#include "sys_io.h"

int sock_socket(int domain, int type, int protocol) __attribute__((weak));
long camkes_sys_socket(va_list ap)
{
    int domain = va_arg(ap, int);
    int type = va_arg(ap, int);
    int protocol = va_arg(ap, int);
    int fd;
    muslcsys_fd_t *fdt;

    if (sock_socket) {
        fd = allocate_fd();
        fdt = get_fd_struct(fd);
        fdt->data = malloc(sizeof(int));
        *(int *)fdt->data = sock_socket(domain, type, protocol);
        fdt->filetype = FILE_TYPE_SOCKET;
        return fd;
    } else {
        assert(!"sys_socket not implemented");
    }

    return 0;
}

int sock_bind(int sockfd, int addrlen) __attribute__((weak));
long camkes_sys_bind(va_list ap)
{
    int fd = va_arg(ap, int);
    const struct sockaddr *addr = va_arg(ap, const struct sockaddr *);
    socklen_t addrlen = va_arg(ap, socklen_t);
    muslcsys_fd_t *fdt;
    int sockfd;

    if (sock_bind && sock_data) {
        fdt = get_fd_struct(fd);
        sockfd = *(int *)fdt->data;
        memcpy((char *)sock_data, addr, addrlen);
        return sock_bind(sockfd, addrlen);
    } else {
        assert(!"sys_bind not implemented");
    }

    return -1;
}

int sock_connect(int sockfd, int addrlen) __attribute__((weak));
long camkes_sys_connect(va_list ap)
{
    int fd = va_arg(ap, int);
    const struct sockaddr *addr = va_arg(ap, const struct sockaddr *);
    socklen_t addrlen = va_arg(ap, socklen_t);

    muslcsys_fd_t *fdt;
    int sockfd;

    if (sock_connect && sock_data) {
        fdt = get_fd_struct(fd);
        sockfd = *(int *)fdt->data;
        memcpy((char *)sock_data, addr, addrlen);
        return sock_connect(sockfd, addrlen);
    } else {
        assert(!"sys_connect not implemented");
    }

    return -1;
}

int sock_listen(int sockfd, int backlog) __attribute__((weak));
long camkes_sys_listen(va_list ap)
{
    int fd = va_arg(ap, int);
    int backlog = va_arg(ap, int);
    muslcsys_fd_t *fdt;
    int sockfd;

    if (sock_listen) {
        fdt = get_fd_struct(fd);
        sockfd = *(int *)fdt->data;
        return sock_listen(sockfd, backlog);
    } else {
        assert(!"sys_listen not implemented");
    }

    return -1;
}

int sock_accept(int sockfd) __attribute__((weak));
long camkes_sys_accept(va_list ap)
{
    int fd = va_arg(ap, int);
    struct sockaddr *addr = va_arg(ap, struct sockaddr *);
    socklen_t *addrlen = va_arg(ap, socklen_t *);

    muslcsys_fd_t *fdt;
    int sockfd;
    int newsockfd;

    if (sock_accept && sock_data) {
        fdt = get_fd_struct(fd);
        sockfd = *(int *)fdt->data;

        /* addr can be NULL, which means ignore the peer address. */
        if (addr) {
            memcpy((char *)sock_data, addr, sizeof(struct sockaddr));
            memcpy((char *)sock_data + sizeof(struct sockaddr), addrlen, sizeof(socklen_t));
        }

        newsockfd = sock_accept(sockfd);

        /* -1 is returned when the call fails. */
        if (newsockfd == -1) {
            memcpy(&errno, (void *)sock_data, sizeof(errno));
            return newsockfd;
        }

        if (addr) {
            memcpy(addr, (char *)sock_data, sizeof(struct sockaddr));
            memcpy(addrlen, (char *)sock_data + sizeof(struct sockaddr), sizeof(socklen_t));
        }

        /*
         * Accept returns a new socket file descriptor, so we need to
         * allocate a new file descriptor.
         */
        fd = allocate_fd();
        fdt = get_fd_struct(fd);
        fdt->data = malloc(sizeof(int));
        *(int *)fdt->data = newsockfd;
        fdt->filetype = FILE_TYPE_SOCKET;

        return fd;
    } else {
        assert(!"sys_accept not implemented");
    }

    return -1;
}

int sock_setsockopt(int sockfd, int level, int optname, int optlen) __attribute__((weak));
long camkes_sys_setsockopt(va_list ap)
{
    int fd = va_arg(ap, int);
    int level = va_arg(ap, int);
    int optname = va_arg(ap, int);
    const void *optval = va_arg(ap, const void *);
    socklen_t optlen = va_arg(ap, socklen_t);

    muslcsys_fd_t *fdt;
    int sockfd;

    if (sock_setsockopt && sock_data) {
        fdt = get_fd_struct(fd);
        sockfd = *(int *)fdt->data;

        memcpy((char *)sock_data, optval, optlen);
        return sock_setsockopt(sockfd, level, optname, optlen);
    } else {
        assert(!"sys_setsockopt not implemented");
    }

    return -1;
}
