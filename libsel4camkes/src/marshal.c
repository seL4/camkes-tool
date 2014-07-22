/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include <stdlib.h>
#include <string.h>
#include <camkes/marshal.h>

void *camkes_marshal(void *buffer, const void *data, unsigned int sz) {
    memcpy(buffer, data, sz);
    return buffer + sz;
}

void *camkes_unmarshal(const void *buffer, void *data, unsigned int sz) {
    memcpy(data, buffer, sz);
    return (void*)(buffer + sz);
}

void *camkes_marshal_string(void *buffer, const char *data) {
    strcpy((char*)buffer, data);
    return buffer + (strlen(data) + 1) * sizeof(char);
}

void *camkes_unmarshal_string(const void *buffer, char *data) {
    strcpy(data, (const char*)buffer);
    return (void*)buffer + (strlen(buffer) + 1) * sizeof(char);
}
