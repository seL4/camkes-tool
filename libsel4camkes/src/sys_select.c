/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/select.h>
#include <muslcsys/io.h>

#include "sys_io.h"

static void fdset_to_sockset(int maxfd, fd_set *fds)
{
	muslcsys_fd_t *fdt;
	int sockfd;

	if (maxfd <= FIRST_USER_FD || !fds) {
		return;
	}

	for (int i = FIRST_USER_FD; i < maxfd; i++) {
		fdt = get_fd_struct(i);
		if (fdt->filetype == FILE_TYPE_SOCKET) {
			sockfd = *(int*)fdt->data;
			if (FD_ISSET(i, fds)) {
				FD_CLR(i, fds);
				FD_SET(sockfd, fds);
			}
		}
	}
}

static void sockset_to_fdset(int maxfd, fd_set *fds)
{
	muslcsys_fd_t *fdt;
	int sockfd;

	if (maxfd <= FIRST_USER_FD || !fds) {
		return;
	}

	for (int i = FIRST_USER_FD; i < maxfd; i++) {
		fdt = get_fd_struct(i);
		if (fdt->filetype == FILE_TYPE_SOCKET) {
			sockfd = *(int*)fdt->data;
			if (FD_ISSET(sockfd, fds)) {
				FD_CLR(sockfd, fds);
				FD_SET(i, fds);
			}
		}
	}
}

static int find_max_sockfd(int nfds)
{
	muslcsys_fd_t *fdt;
	int sockfd;
	int max = 0;

	for (int i = FIRST_USER_FD; i < nfds; i++) {
		fdt = get_fd_struct(i);
		if (fdt->filetype == FILE_TYPE_SOCKET) {
			sockfd = *(int*)fdt->data;
			if (sockfd > max) {
				max = sockfd;
			}
		}
	}

	return max;
}

int sock_select(int nfds) __attribute__((weak));
long camkes_sys__newselect(va_list ap)
{
	int nfds = va_arg(ap, int);
	fd_set *readfds = va_arg(ap, fd_set*);
	fd_set *writefds = va_arg(ap, fd_set*);
	fd_set *exceptfds = va_arg(ap, fd_set*);
	struct timeval *timeout = va_arg(ap, struct timeval*);
	int retval;

	if (sock_select && sock_data) {
		fdset_to_sockset(nfds, readfds);
		fdset_to_sockset(nfds, writefds);
		fdset_to_sockset(nfds, exceptfds);

		if (readfds) {
			memcpy((char*)sock_data, readfds, sizeof(fd_set));
		}

		if (writefds) {
			memcpy((char*)sock_data + sizeof(fd_set), writefds, sizeof(fd_set));
		}

		if (exceptfds) {
			memcpy((char*)sock_data + sizeof(fd_set) * 2, exceptfds, sizeof(fd_set));
		}

		if (timeout) {
			memcpy((char*)sock_data + sizeof(fd_set) * 3, timeout, sizeof(struct timeval));
		}

		retval = sock_select(find_max_sockfd(nfds) + 1);

		if (readfds) {
			memcpy(readfds, (char*)sock_data, sizeof(fd_set));
		}

		if (writefds) {
			memcpy(writefds, (char*)sock_data + sizeof(fd_set), sizeof(fd_set));
		}

		if (exceptfds) {
			memcpy(exceptfds, (char*)sock_data + sizeof(fd_set) * 2, sizeof(fd_set));
		}

		if (timeout) {
			memcpy(timeout, (char*)sock_data + sizeof(fd_set) * 3, sizeof(struct timeval));
		}

		sockset_to_fdset(nfds, readfds);
		sockset_to_fdset(nfds, writefds);
		sockset_to_fdset(nfds, exceptfds);

		return retval;

	} else {
		assert(!"sys__newselect not implemented");
        return -ENOSYS;
	}
}
