/*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef _CAMKES_IO_H_
#define _CAMKES_IO_H_

#include <platsupport/io.h>
#include <stdint.h>

/* Initialise an IO mapper for use with libplatsupport. Returns 0 on success.
 */
int camkes_io_mapper(ps_io_mapper_t *mapper);

/* Initialise an IO port accessor for use with libplatsupport. Returns 0 on
 * success.
 */
int camkes_io_port_ops(ps_io_port_ops_t *ops);

/* Initialise an IO operations object for use with libplatsupport. Returns 0 on
 * success.
 */
int camkes_io_ops(ps_io_ops_t *ops);

#endif
