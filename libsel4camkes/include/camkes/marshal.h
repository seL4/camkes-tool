/*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef _CAMKES_MARSHAL_H_
#define _CAMKES_MARSHAL_H_

void *camkes_marshal(void *buffer, const void *data, unsigned sz);
void *camkes_unmarshal(const void *buffer, void *data, unsigned sz);
void *camkes_marshal_string(void *buffer, const char *data);
void *camkes_unmarshal_string(const void *buffer, char *data);

#endif /* !_CAMKES_MARSHAL_H_ */
