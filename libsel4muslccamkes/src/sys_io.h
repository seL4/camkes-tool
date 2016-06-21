/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef __LIBSEL4MUSLCCAMKES_H__
#define __LIBSEL4MUSLCCAMKES_H__

#include <utils/page.h>

#define STDOUT_FD     1
#define STDERR_FD     2
#define FIRST_USER_FD 3

#define FILE_TYPE_SOCKET  1 

#define FD_TABLE_SIZE(x) (sizeof(muslcsys_fd_t) * (x))
/* this implementation does not allow users to close STDOUT or STDERR, so they can't be freed */
#define FREE_FD_TABLE_SIZE(x) (sizeof(int) * ((x) - FIRST_USER_FD))

typedef struct muslcsys_fd {
    int filetype;
    void *data;
} muslcsys_fd_t;

int allocate_fd(void);

muslcsys_fd_t *get_fd_struct(int fd);

/* CAmkES dataport for socket interface. */
extern volatile char sock_data_data[PAGE_SIZE_4K] __attribute__((weak));

#endif
