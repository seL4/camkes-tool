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
 *
 */

/*# Example template for receiving an RPC message. This template is not
 *# intended to be used as-is, but is a guide for implementing your own RPC
 *# templates. Note that error handling has been elided.
 #*/

#define IPC_BUFFER ((void*)&(seL4_GetIPCBuffer()->mr[0]))

#define MARSHAL(dst, src) \
    do { \
        memcpy(dst, &(src), sizeof(src)); \
        dst += sizeof(src); \
    } while (0)

#define UNMARSHAL(src, dst) \
    do { \
        memcpy(&(dst), src, sizeof(dst)); \
        src += sizeof(dst); \
    } while (0)

/*- for m in me.methods -*/

extern /*? m.return_type or 'void' ?*/ /*? m.name ?*/(seL4_Word _badge
    /*- if len(m.parameters) > 0 -*/
        ,
    /*- endif -*/
    /*- for p in m.parameters -*/
        /*? p.type ?*/
        /*- if p.direction in ['out', 'inout'] -*/
            *
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
);

static unsigned handle_/*? m.name ?*/(seL4_Word _badge) {
    void *_buffer = IPC_BUFFER;
    /* skip over method index */
    _buffer += sizeof(unsigned);

    /* Unmarshal the inputs */
    /*- for p in m.parameters -*/
        /*? p.type ?*/ /*? p.name ?*/;
        /*- if p.direction in ['in', 'inout'] -*/
            UNMARSHAL(_buffer, /*? p.name ?*/);
        /*- endif -*/
    /*- endfor -*/

    /* Call the user's function */
    /*- if m.return_type -*/
        /*? m.return_type ?*/ _ret =
    /*- endif -*/
    /*? m.name ?*/(_badge,
    /*- for p in m.parameters -*/
        /*- if p.direction in ['out', 'inout'] -*/
            &
        /*- endif -*/
        /*? p.name ?*/
        /*- if not loop.last -*/
            ,
        /*- endif -*/
    /*- endfor -*/
    );

    /* Marshal the response */
    _buffer = IPC_BUFFER;
    /*- if m.return_type -*/
        MARSHAL(_buffer, _ret);
    /*- endif -*/
    /*- for p in m.parameters -*/
        /*- if p.direction in ['out', 'inout'] -*/
            MARSHAL(_buffer, /*? p.name ?*/);
        /*- endif -*/
    /*- endfor -*/

    return ROUND_UP(_buffer - IPC_BUFFER, 2);
}

/*- endfor -*/

int run_/*? p.name ?*/(seL4_CPtr _ep) {
    while (true) {
        seL4_Word _badge;
        seL4_MessageInfo_t _info = seL4_Recv(_ep, &_badge);
        unsigned _method_index = seL4_GetMR(0);
        switch (_method_index) {
            /*- for i, m in enumerate(me.methods) -*/
                case /*? i ?*/:;
                    unsigned length = handle_/*? m.name ?*/(_badge);
                    _info = seL4_MessageInfo_new(0, 0, 0, length);
                    break;
            /*- endfor -*/
                default:
                    return -1;
        }
        seL4_Send(_ep, _info);
    }
}
