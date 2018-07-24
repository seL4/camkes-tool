/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <string.h>
#include <sel4/sel4.h>
#include <camkes/tls.h>

#define FFI_SUCCESS 0

void fficamkes_declare_reply_cap(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t slot;
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
    uint64_t cnode;
    memcpy(&cnode, a, sizeof(cnode));
    camkes_get_tls()->cnode_cap = cnode;
    a[0] = FFI_SUCCESS;
}

void ffiseL4_Recv(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t ep;
    memcpy(&ep, a + 1, sizeof(ep));
    uint64_t badge;
    seL4_MessageInfo_t info = seL4_Recv(ep, &badge);
    uint64_t len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    memcpy(a + 1, &len, sizeof(len));
    memcpy(a + 9, &badge, sizeof(badge));
    memcpy(a + 17, &seL4_GetIPCBuffer()->msg[0], len);
    a[0] = FFI_SUCCESS;
}

void ffiseL4_ReplyRecv(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t ep;
    memcpy(&ep, a + 1, sizeof(ep));
    uint64_t len;
    memcpy(&len, a + 9, sizeof(len));
    uint64_t badge;
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + 17, len);
    seL4_MessageInfo_t info = seL4_ReplyRecv(
        ep,
        seL4_MessageInfo_new(0, 0, 0, ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) / sizeof(seL4_Word)),
        &badge);
    len = seL4_MessageInfo_get_length(info) * sizeof(seL4_Word);
    memcpy(a + 1, &len, sizeof(len));
    memcpy(a + 9, &badge, sizeof(badge));
    memcpy(a + 17, &seL4_GetIPCBuffer()->msg[0], len);
    a[0] = FFI_SUCCESS;
}

void ffiseL4_Send(unsigned char *c, long clen, unsigned char *a, long alen) {
    uint64_t ep;
    memcpy(&ep, a + 1, sizeof(ep));
    uint64_t len;
    memcpy(&len, a + 9, sizeof(len));
    memcpy(&seL4_GetIPCBuffer()->msg[0], a + 17, len);
    seL4_Send(
        ep,
        seL4_MessageInfo_new(0, 0, 0, ROUND_UP_UNSAFE(len, sizeof(seL4_Word)) / sizeof(seL4_Word)));
    a[0] = FFI_SUCCESS;
}
