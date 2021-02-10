/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <sel4/sel4.h>
#include <camkes/tls.h>

#define FFI_SUCCESS 0

void fficamkes_declare_reply_cap(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr slot;
    memcpy(&slot, a + 1, sizeof(slot));
    camkes_declare_reply_cap(slot);
    a[0] = FFI_SUCCESS;
}

void fficlear_tls_reply_cap_in_tcb(unsigned char *c, long clen, unsigned char *a, long alen) {
    camkes_tls_t *tls = camkes_get_tls();
    if (tls->reply_cap_in_tcb) {
        tls->reply_cap_in_tcb = false;
        a[1] = 1;
    } else {
        camkes_unprotect_reply_cap();
        a[1] = 0;
    }
    a[0] = FFI_SUCCESS;
}

void ffiset_tls_cnode_cap(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr cnode;
    memcpy(&cnode, a, sizeof(cnode));
    camkes_get_tls()->cnode_cap = cnode;
    a[0] = FFI_SUCCESS;
}

void ffiseL4_Recv(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr ep;
    memcpy(&ep, a + 1, sizeof(ep));
    seL4_Word badge;
    seL4_MessageInfo_t info = seL4_Recv(ep, &badge);
    seL4_Word len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    int offset = 1;
	memcpy(a + offset, &len, sizeof(len));
	offset += sizeof(len);
    memcpy(a + offset, &badge, sizeof(badge));
	offset += sizeof(badge);
    memcpy(a + offset, &seL4_GetIPCBuffer()->msg[0], len);
	a[0] = FFI_SUCCESS;
}

void ffiseL4_ReplyRecv(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr ep;
    int offset = 1;
    memcpy(&ep, a + offset, sizeof(ep));
    offset += sizeof(ep);
    seL4_Word len;
    memcpy(&len, a + offset, sizeof(len));
    offset += sizeof(len);
    seL4_Word badge;
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + offset, len);
    seL4_MessageInfo_t info = seL4_ReplyRecv(
        ep,
        seL4_MessageInfo_new(0, 0, 0, ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) / sizeof(seL4_Word)),
        &badge);
    len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    offset = 1;
    memcpy(a + offset, &len, sizeof(len));
    offset += sizeof(len);
    memcpy(a + offset, &badge, sizeof(badge));
    offset += sizeof(badge);
    memcpy(a + offset, &seL4_GetIPCBuffer()->msg[0], len);
    a[0] = FFI_SUCCESS;
}

void ffiseL4_Send(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr ep;
    int offset = 1;
    memcpy(&ep, a + offset, sizeof(ep));
    offset += sizeof(ep);
    seL4_Word len;
    memcpy(&len, a + offset, sizeof(len));
    offset += sizeof(len);
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + offset, len);
    seL4_Send(
        ep,
        seL4_MessageInfo_new(0, 0, 0, ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) / sizeof(seL4_Word)));
    a[0] = FFI_SUCCESS;
}

// Wait on an seL4 notification or endpoint
void ffiseL4_Wait(unsigned char *c, long clen, unsigned char *a, long alen) {
    seL4_CPtr src;
    memcpy(&src, a + 1, sizeof(src));
    seL4_Word badge;
    seL4_Wait(src, &badge);
    memcpy(a + 1, &badge, sizeof(badge));
    a[0] = FFI_SUCCESS;
}
