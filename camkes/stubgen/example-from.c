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

/*# Example template for sending an RPC message. This template is not
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

/*- for i, m in enumerate(me.methods) -*/

/*? m.return_type or 'void' ?*/ /*? m.name ?*/(seL4_CPtr _ep
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
) {
    /* Marshal all the inputs */
    void *_buffer = IPC_BUFFER;
    unsigned _method_index = /*? i ?*/;
    MARSHAL(_buffer, _method_index);
    /*- for p in m.parameters -*/
        /*- if p.direction == 'in' -*/
            MARSHAL(_buffer, /*? p.name ?*/);
        /*- elif p.direction == 'inout' -*/
            MARSHAL(_buffer, * /*? p.name ?*/);
        /*- endif -*/
    /*- endfor -*/

    /* Perform the IPC */
    seL4_MessageInfo_t _info =
        seL4_MessageInfo_new(0, 0, 0, ROUND_UP(_buffer - IPC_BUFFER, 2));
    seL4_Send(_ep, _info);
    _info = seL4_Recv(_ep, NULL);

    /* Unmarshal the outputs */
    _buffer = IPC_BUFFER;
    /*- if m.return_type -*/
        /*? m.return_type ?*/ _ret;
        UNMARSHAL(_buffer, _ret);
    /*- endif -*/
    /*- for p in m.parameters -*/
        /*- if p.direction in ['out', 'inout'] -*/
            UNMARSHAL(_buffer, * /*? p.name ?*/);
        /*- endif -*/
    /*- endfor -*/
    /*- if m.return_type -*/
        return _ret;
    /*- endif -*/
}

/*- endfor -*/
