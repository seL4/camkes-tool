/*#
 *# Copyright 2015, NICTA
 *#
 *# This software may be distributed and modified according to the terms of
 *# the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *# See "LICENSE_BSD2.txt" for details.
 *#
 *# @TAG(NICTA_BSD)
 #*/

#include <autoconf.h>
#include <assert.h>
#include <camkes.h> /* generated header */
#include <platsupport/io.h>
#include <sel4/types.h>
#include <sel4/sel4.h>
#include <sync/mutex.h>
#include <sync/sem.h>
#include <sel4platsupport/platsupport.h>
#include <camkes/allocator.h>
#include <camkes/dataport.h>
#include <camkes/dma.h>
#include <camkes/error.h>
#include <camkes/fault.h>
#include <camkes/io.h>
#include <camkes/tls.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sync/sem-bare.h>
#include <sel4debug/identity.h>
#include <sel4utils/mapping.h>
#include <utils/util.h>

/*? macros.show_includes(me.type.includes) ?*/

/*- set putchar = c_symbol() -*/
static void (* /*? putchar ?*/)(int c);

void set_putchar(void (*putchar)(int c)) {
    /*? putchar ?*/ = putchar;
}

void __arch_putchar(int c) {
    if (/*? putchar ?*/ != NULL) {
        /*? putchar ?*/(c);
        return;
    }
#ifdef SEL4_DEBUG_KERNEL
    seL4_DebugPutChar(c);
#endif
}

const char *get_instance_name(void) {
    static const char name[] = "/*? me.name ?*/";
    return name;
}

/* DMA functionality. */

/*# Determine the size of the DMA pool. Note that we make no attempt to
 *# suppress this attribute being generated as a user-accessible variable at
 *# the top of this file. If the component actually has a declared attribute
 *# 'dma_pool' then they will get access to this variable at runtime.
 #*/
/*- set dma_pool = macros.ROUND_UP(configuration[me.name].get('dma_pool', 0), macros.PAGE_SIZE) -*/
/*- set page_size = [macros.PAGE_SIZE] -*/
/*- if options.largeframe_dma -*/
  /*- for sz in reversed(macros.page_sizes(options.architecture)) -*/
    /*- if dma_pool >= sz -*/
      /*- do page_size.__setitem__(0, sz) -*/
      /*- break -*/
    /*- endif -*/
  /*- endfor -*/
/*- endif -*/

/*- set p = Perspective() -*/
static char /*? p['dma_pool_symbol'] ?*/[/*? dma_pool ?*/]
    __attribute__((section("persistent")))
    ALIGN(/*? page_size[0] ?*/);

/*- set get_paddr = c_symbol('get_paddr') -*/
uintptr_t /*? get_paddr ?*/(void *ptr) {
    uintptr_t base UNUSED = (uintptr_t)ptr & ~MASK(ffs(/*? page_size[0] ?*/) - 1);
    uintptr_t offset UNUSED = (uintptr_t)ptr & MASK(ffs(/*? page_size[0] ?*/) - 1);
    /*- for i in six.moves.range(int(macros.ROUND_UP(dma_pool, page_size[0]) // page_size[0])) -*/
        /*- if not loop.first -*/
            else
        /*- endif -*/
        if (base == (uintptr_t)/*? p['dma_pool_symbol'] ?*/ + /*? i ?*/ * /*? page_size[0] ?*/) {
            /*- set p = Perspective(dma_frame_index=i) -*/
            /*- set frame = alloc(p['dma_frame_symbol'], seL4_FrameObject, size=page_size[0]) -*/
            /*- set paddr_sym = c_symbol('paddr') -*/
            static uintptr_t /*? paddr_sym ?*/;
            if (/*? paddr_sym ?*/ == 0) {
                seL4_ARCH_Page_GetAddress_t res = seL4_ARCH_Page_GetAddress(/*? frame ?*/);
                ERR_IF(res.error != 0, camkes_error, ((camkes_error_t){
                        .type = CE_SYSCALL_FAILED,
                        .instance = "/*? me.name ?*/",
                        .description = "failed to reverse virtual mapping to a DMA frame",
                        .syscall = ARCHPageGetAddress,
                        .error = res.error,
                    }), ({
                        return (uintptr_t)NULL;
                    }));
                /*? paddr_sym ?*/ = res.paddr;
            }
            return /*? paddr_sym ?*/ + offset;
        }
    /*- endfor -*/
    return (uintptr_t)NULL;
}

/* MMIO related functionality for interaction with libplatsupport. */
void *camkes_io_map(void *cookie UNUSED, uintptr_t paddr UNUSED,
        size_t size UNUSED, int cached UNUSED, ps_mem_flags_t flags UNUSED) {

    /*- for d in me.type.dataports -*/
        extern void * /*? d.name ?*/_translate_paddr(uintptr_t paddr,
            size_t size) WEAK;
        if (/*? d.name ?*/_translate_paddr != NULL) {
            void *p = /*? d.name ?*/_translate_paddr(paddr, size);
            if (p != NULL) {
                return p;
            }
        }
    /*- endfor -*/

    /* Not found. */
    return NULL;
}

/* IO port related functionality for interaction with libplatsupport. */
int camkes_io_port_in(void *cookie UNUSED, uint32_t port UNUSED,
        int io_size UNUSED, uint32_t *result UNUSED) {
    /*- for u in me.type.uses -*/
        /*- if u.type.name == 'IOPort' -*/ /*# XXX: awkward hardcoding of connector type name #*/
            if (/*? u.name ?*/_in_range(port)) {
                switch (io_size) {
                    case 1:
                        *result = /*? u.name ?*/_in8(port);
                        return 0;
                    case 2:
                        *result = /*? u.name ?*/_in16(port);
                        return 0;
                    case 4:
                        *result = /*? u.name ?*/_in32(port);
                        return 0;
                }
                return -1;
            }
        /*- endif -*/
    /*- endfor -*/
    return -1;
}
int camkes_io_port_out(void *cookie UNUSED, uint32_t port UNUSED,
        int io_size UNUSED, uint32_t val UNUSED) {
    /*- for u in me.type.uses -*/
        /*- if u.type.name == 'IOPort' -*/ /*# XXX: awkward hardcoding of connector type name #*/
            if (/*? u.name ?*/_in_range(port)) {
                switch (io_size) {
                    case 1:
                        /*? u.name ?*/_out8(port, val);
                        return 0;
                    case 2:
                        /*? u.name ?*/_out16(port, val);
                        return 0;
                    case 4:
                        /*? u.name ?*/_out32(port, val);
                        return 0;
                }
                return -1;
            }
        /*- endif -*/
    /*- endfor -*/
    return -1;
}

/* Mutex functionality. */
/*- for m in me.type.mutexes -*/

/*- set mutex = c_symbol(m.name) -*/
static sync_mutex_t /*? mutex ?*/;

static int mutex_/*? m.name ?*/_init(void) {
    /*- set aep = alloc(m.name, seL4_NotificationObject, read=True, write=True) -*/
    return sync_mutex_init(&/*? mutex ?*/, /*? aep ?*/);
}

int /*? m.name ?*/_lock(void) {
    return sync_mutex_lock(&/*? mutex ?*/);
}

int /*? m.name ?*/_unlock(void) {
    return sync_mutex_unlock(&/*? mutex ?*/);
}

/*- endfor -*/

/* Semaphore functionality. */
/*- for s in me.type.semaphores -*/

/*- set semaphore = c_symbol(s.name) -*/
static sync_sem_t /*? semaphore ?*/;

static int semaphore_/*? s.name ?*/_init(void) {
    /*- set ep = alloc(s.name, seL4_EndpointObject, read=True, write=True) -*/
    return sync_sem_init(&/*? semaphore ?*/, /*? ep ?*/,
        /*? configuration[me.name].get('%s_value' % s.name, 1) ?*/);
}

int /*? s.name ?*/_wait(void) {
    camkes_protect_reply_cap();
    return sync_sem_wait(&/*? semaphore ?*/);
}

int /*? s.name ?*/_trywait(void) {
    return sync_sem_trywait(&/*? semaphore ?*/);
}

int /*? s.name ?*/_post(void) {
    return sync_sem_post(&/*? semaphore ?*/);
}

/*- endfor -*/

#ifndef CONFIG_CAMKES_DEFAULT_HEAP_SIZE
#define CONFIG_CAMKES_DEFAULT_HEAP_SIZE 1048576
#endif

/*- set heap_size = configuration[me.name].get('heap_size', 'CONFIG_CAMKES_DEFAULT_HEAP_SIZE') -*/

/*- set heap = c_symbol() -*/
#if /*? heap_size ?*/ > 0
static char /*? heap ?*/[/*? heap_size ?*/];
extern char *morecore_area;
extern size_t morecore_size;
#endif

/* General CAmkES platform initialisation. Expects to be run in a
 * single-threaded, exclusive context. On failure it does not return.
 */
/*- set init = c_symbol() -*/
static void /*? init ?*/(void) {
#if /*? heap_size ?*/ > 0
    /* Assign the heap */
    morecore_area = /*? heap ?*/;
    morecore_size = /*? heap_size ?*/;
#endif

    /* The user has actually had no opportunity to install any error handlers at
     * this point, so any error triggered below will certainly be fatal.
     */
    int res = camkes_dma_init(/*? p['dma_pool_symbol'] ?*/, /*? dma_pool ?*/,
        /*? page_size[0] ?*/, /*? get_paddr ?*/);
    ERR_IF(res != 0, camkes_error, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? me.name ?*/",
            .description = "DMA initialisation failed",
        }), ({
            return;
        }));
    debug_set_id_fn(get_instance_name);
    /*- for m in me.type.mutexes -*/
        res = mutex_/*? m.name ?*/_init();
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "initialisation of mutex \"/*? m.name ?*/\" failed",
            }), ({
                return;
            }));
    /*- endfor -*/
    /*- for s in me.type.semaphores -*/
        res = semaphore_/*? s.name ?*/_init();
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "initialisation of semaphore \"/*? s.name ?*/\" failed",
            }), ({
                return;
            }));
    /*- endfor -*/

    /* Initialise cap allocator. */
    /*- set tcb_pool = configuration[me.name].get('tcb_pool', 0) -*/
    /*- for i in six.moves.range(tcb_pool) -*/
        /*- set tcb = alloc('tcb_pool_%d' % i, seL4_TCBObject, read=True, write=True) -*/
        res = camkes_provide(seL4_TCBObject, /*? tcb ?*/, 0, seL4_CanRead|seL4_CanWrite);
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "failed to add TCB /*? tcb + 1 ?*/ to cap allocation pool",
            }), ({
                return;
            }));
    /*- endfor -*/
    /*- set ep_pool = configuration[me.name].get('ep_pool', 0) -*/
    /*- for i in six.moves.range(ep_pool) -*/
        /*- set ep = alloc('ep_pool_%d' % i, seL4_EndpointObject, read=True, write=True) -*/
        res = camkes_provide(seL4_EndpointObject, /*? ep ?*/, 0, seL4_CanRead|seL4_CanWrite);
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "failed to add EP /*? ep + 1 ?*/ to cap allocation pool",
            }), ({
                return;
            }));
    /*- endfor -*/
    /*- set aep_pool = configuration[me.name].get('aep_pool', 0) -*/
    /*- for i in six.moves.range(aep_pool) -*/
        /*- set aep = alloc('aep_pool_%d' % i, seL4_NotificationObject, read=True, write=True) -*/
        res = camkes_provide(seL4_NotificationObject, /*? aep ?*/, 0, seL4_CanRead|seL4_CanWrite);
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "failed to add AEP /*? aep + 1 ?*/ to cap allocation pool",
            }), ({
                return;
            }));
    /*- endfor -*/
    /*- set untyped_pool = [] -*/
    /*- for attribute, value in configuration[me.name].items() -*/
        /*- set r = re.match('untyped(\\d+)_pool$', attribute) -*/
        /*- if r is not none -*/
            /*- do untyped_pool.append((r.group(1), value)) -*/
        /*- endif -*/
    /*- endfor -*/
    /*- for u in untyped_pool -*/
        /*- for i in six.moves.range(u[1]) -*/
            /*- if not 4 <= int(u[0]) <= 28 -*/
                /*? raise(TemplateError('illegal untyped size')) ?*/
            /*- endif -*/
            /*- set untyped = alloc('untyped_%s_pool_%d' % (u[0], i), seL4_UntypedObject, size_bits=int(u[0]), read=True, write=True) -*/
            res = camkes_provide(seL4_UntypedObject, /*? untyped ?*/, 1U << /*? u[0] ?*/, seL4_CanRead|seL4_CanWrite);
            ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                    .type = CE_ALLOCATION_FAILURE,
                    .instance = "/*? me.name ?*/",
                    .description = "failed to add untyped /*? untyped + 1 ?*/ of size /*? u[0] ?*/ bits to cap allocation pool",
                }), ({
                    return;
                }));
        /*- endfor -*/
    /*- endfor -*/
}

#ifndef CONFIG_CAMKES_DEFAULT_STACK_SIZE
    #define CONFIG_CAMKES_DEFAULT_STACK_SIZE PAGE_SIZE_4K
#endif

/*- for i in me.type.provides + me.type.uses -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/

/*- set threads = macros.threads(composition, me) -*/

/* Thread stacks */
/*- set p = Perspective(instance=me.name, control=True) -*/
/*- set stack_size = configuration[me.name].get('_stack_size', 'CONFIG_CAMKES_DEFAULT_STACK_SIZE') -*/
/*? macros.thread_stack(p['stack_symbol'], stack_size) ?*/
/*- for t in threads[1:] -*/
    /*- set p = Perspective(instance=me.name, interface=t.interface.name, intra_index=t.intra_index) -*/
    /*- set stack_size = configuration[me.name].get('%s_stack_size' % t.interface.name, 'CONFIG_CAMKES_DEFAULT_STACK_SIZE') -*/
    /*? macros.thread_stack(p['stack_symbol'], stack_size) ?*/
/*- endfor -*/
/*- if options.debug_fault_handlers -*/
    /*- set p = Perspective(instance=me.name, interface='0_fault_handler', intra_index=0) -*/
    /*? macros.thread_stack(p['stack_symbol'], 'CONFIG_CAMKES_DEFAULT_STACK_SIZE') ?*/
/*- endif -*/

/* IPC buffers */
/*- set p = Perspective(instance=me.name, control=True) -*/
/*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- for t in threads[1:] -*/
    /*- set p = Perspective(instance=me.name, interface=t.interface.name, intra_index=t.intra_index) -*/
    /*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- endfor -*/
/*- if options.debug_fault_handlers -*/
    /*- set p = Perspective(instance=me.name, interface='0_fault_handler', intra_index=0) -*/
    /*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- endif -*/

/* Attributes */
/*- set myconf = configuration[me.name] -*/
/*- for a in me.type.attributes -*/
    /*- set value = myconf.get(a.name) -*/
    /*- if value is not none -*/
        const /*? macros.show_type(a.type) ?*/ /*? a.name ?*/ =
        /*- if isinstance(value, six.string_types) -*/
            "/*? value ?*/"
        /*- else -*/
            /*? value ?*/
        /*- endif -*/
        ;
    /*- endif -*/
/*- endfor -*/

/*- if options.debug_fault_handlers -*/
  /*- set fault_ep = alloc_obj('fault_ep', seL4_EndpointObject) -*/
/*- endif -*/

/* This function is called from crt0.S *prior* to `main`. */
void USED _camkes_tls_init(int thread_id) {
    switch (thread_id) {
        /*- set _tcb_control = alloc_obj('%d_0_control_%d_tcb' % (len(me.name), len('0_control')), seL4_TCBObject) -*/
        /*- set tcb_control = alloc_cap('%d_0_control_%d_tcb' % (len(me.name), len('0_control')), _tcb_control) -*/
        /*- if options.debug_fault_handlers -*/
          /*? assert(fault_ep is defined and fault_ep is not none) ?*/
          /*- set fault_ep_cap = alloc_cap('fault_ep_0_control', fault_ep, read=True, write=True, grant=True) -*/
          /*- do my_cnode[fault_ep_cap].set_badge(tcb_control) -*/
          /*- do setattr(_tcb_control, 'fault_ep_slot', fault_ep_cap) -*/
        /*- endif -*/
        case /*? tcb_control ?*/ : /* Control thread */
            /*- set p = Perspective(instance=me.name, control=True) -*/
            /*? macros.save_ipc_buffer_address(p['ipc_buffer_symbol']) ?*/
            camkes_get_tls()->tcb_cap = /*? tcb_control ?*/;
            camkes_get_tls()->thread_index = 1;
            break;

        /*# Interface threads #*/
        /*- for index, t in enumerate(threads[1:]) -*/
            /*- set _tcb = alloc_obj('%d_%s_%d_%04d_tcb' % (len(me.name), t.interface.name, len(t.interface.name), t.intra_index), seL4_TCBObject) -*/
            /*- set tcb = alloc_cap('%d_%s_%d_%04d_tcb' % (len(me.name), t.interface.name, len(t.interface.name), t.intra_index), _tcb) -*/
            /*- if options.debug_fault_handlers -*/
              /*? assert(fault_ep is defined and fault_ep is not none) ?*/
              /*- set fault_ep_cap = alloc_cap('fault_ep_%s_%04d' % (t.interface.name, t.intra_index), fault_ep, read=True, write=True, grant=True) -*/
              /*- do my_cnode[fault_ep_cap].set_badge(tcb) -*/
              /*- do setattr(_tcb, 'fault_ep_slot', fault_ep_cap) -*/
            /*- endif -*/
            case /*? tcb ?*/ : { /* Interface /*? t.interface.name ?*/ */
                /*- set p = Perspective(instance=me.name, interface=t.interface.name, intra_index=t.intra_index) -*/
                /*? macros.save_ipc_buffer_address(p['ipc_buffer_symbol']) ?*/
                camkes_get_tls()->tcb_cap = /*? tcb ?*/;
                camkes_get_tls()->thread_index = /*? index ?*/ + 2;
                break;
            }
        /*- endfor -*/

        /*- if options.debug_fault_handlers -*/
            /*- set tcb = alloc('%d_0_fault_handler_%d_0000_tcb' % (len(me.name), len('0_fault_handler')), seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Fault handler thread */
                /*- set p = Perspective(instance=me.name, interface='0_fault_handler', intra_index=0) -*/
                /*? macros.save_ipc_buffer_address(p['ipc_buffer_symbol']) ?*/
                camkes_get_tls()->tcb_cap = /*? tcb ?*/;
                camkes_get_tls()->thread_index = /*? len(threads) ?*/ + 1;
                break;
            }
        /*- endif -*/

        default:
            assert(!"invalid thread ID");
    }
}

/*- if options.debug_fault_handlers -*/
    /*- set fault_handler = c_symbol('fault_handler') -*/
    static void /*? fault_handler ?*/(void) UNUSED NORETURN;
    static void /*? fault_handler ?*/(void) {
        while (true) {
            seL4_Word badge;

            /* Wait for a fault from one of the component's threads. */
            /*- set fault_ep_cap = alloc_cap('fault_ep__fault_handler', fault_ep, read=True, write=True, grant=True) -*/
            seL4_MessageInfo_t info = seL4_Recv(/*? fault_ep_cap ?*/, &badge);

            /* Various symbols that are provided by the linker script. */
            extern char __executable_start[1];
            extern char guarded[1] UNUSED;
            extern char persistent[1] UNUSED;
            extern char _end[1] UNUSED;

            /* Thread name and address space map relevant for this fault. Note
             * that we describe a simplified version of the component's address
             * space below (e.g. we only describe the stack of the current
             * thread). The assumption is that the full address space will
             * confuse the user and most likely not be relevant for diagnosing
             * the fault. E.g. you may have faulted on another thread's guard
             * page, which will not be revealed to you in the memory map, but
             * it is unlikely this information will help you diagnose the cause
             * of the fault anyway.
             */
            const char *thread_name;
            const camkes_memory_region_t *memory_map;

            /* Each of the component's threads have a badged endpoint, so we
             * can determine from the badge of the message we just received
             * which thread was responsible for the fault.
             */
            switch (badge) {

                /*- set tcb_control = alloc('%d_0_control_%d_tcb' % (len(me.name), len('0_control')), seL4_TCBObject) -*/
                /*- set p = Perspective(instance=me.name, control=True) -*/
                case /*? tcb_control ?*/ : {
                    thread_name = "control";
                    /*- if options.architecture in ('arm', 'arm_hyp') and options.largeframe_dma and page_size[0] > 2 ** 15 -*/
                      /*# XXX: The short version is, we can't do accurate memory maps under these
                       *# circumstances.
                       *#
                       *# The long version is, with a large DMA pool, the DMA pool array needs to be
                       *# aligned to the (large) page size in use. On ARM, for reasons that are
                       *# unclear to me, GAS rejects alignment constraints beyond 15-bit. CAmkES
                       *# contains a compiler wrapper and build system support for working around
                       *# this by detecting such an issue and calling Clang, which does not have
                       *# this limitation. Unfortunately this prevents the section symbols,
                       *# `guarded` and `persistent` from being visible at runtime. To cope with
                       *# this, we can mark them as weak and do runtime detection of their
                       *# existence. However, all my attempts to do this have resulted in the linker
                       *# segfaulting while trying to build the component. Instead of continuing
                       *# down this dark and ever-narrowing road, we just provide an inaccurate
                       *# memory map. Sorry, folks.
                       #*/
                      memory_map = (camkes_memory_region_t[]){
                          { .start = (uintptr_t)__executable_start,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ - 1,
                            .name = "code and data" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                            .name = "stack" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                            .name = "IPC buffer" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - 1,
                            .name = "guard page" },
                          { .start = 0, .end = 0, .name = NULL },
                      };
                    /*- else -*/
                      memory_map = (camkes_memory_region_t[]){
                          { .start = (uintptr_t)__executable_start,
                            .end = (uintptr_t)guarded - 1,
                            .name = "code and data" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                            .name = "stack" },
                          { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                              sizeof(/*? p['stack_symbol'] ?*/) - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                            .name = "guard page" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                            .name = "IPC buffer" },
                          { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K,
                            .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                              sizeof(/*? p['ipc_buffer_symbol'] ?*/) - 1,
                            .name = "guard page" },
                          { .start = persistent == _end ? 0 : (uintptr_t)persistent,
                            .end = persistent == _end ? 0 : (uintptr_t)_end,
                            .name = "data" },
                          { .start = 0, .end = 0, .name = NULL },
                      };
                    /*- endif -*/
                    break;
                }

                /*- for t in threads[1:] -*/
                    /*- set tcb = alloc('%d_%s_%d_%04d_tcb' % (len(me.name), t.interface.name, len(t.interface.name), t.intra_index), seL4_TCBObject) -*/
                    /*- set p = Perspective(instance=me.name, interface=t.interface.name, intra_index=t.intra_index) -*/
                    case /*? tcb ?*/ : {
                        thread_name = "/*? t.interface.name ?*/";
                        /*- if options.architecture in ('arm', 'arm_hyp') and options.largeframe_dma and page_size[0] > 2 ** 15 -*/
                          /*# See comment above. #*/
                          memory_map = (camkes_memory_region_t[]){
                              { .start = (uintptr_t)__executable_start,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ - 1,
                                .name = "code and data" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                                .name = "stack" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                                .name = "IPC buffer" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - 1,
                                .name = "guard page" },
                              { .start = 0, .end = 0, .name = NULL },
                          };
                        /*- else -*/
                          memory_map = (camkes_memory_region_t[]){
                              { .start = (uintptr_t)__executable_start,
                                .end = (uintptr_t)guarded - 1,
                                .name = "code and data" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ + PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                                .name = "stack" },
                              { .start = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['stack_symbol'] ?*/ +
                                  sizeof(/*? p['stack_symbol'] ?*/) - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K - 1,
                                .name = "guard page" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ + PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K - 1,
                                .name = "IPC buffer" },
                              { .start = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - PAGE_SIZE_4K,
                                .end = (uintptr_t)&/*? p['ipc_buffer_symbol'] ?*/ +
                                  sizeof(/*? p['ipc_buffer_symbol'] ?*/) - 1,
                                .name = "guard page" },
                              { .start = persistent == _end ? 0 : (uintptr_t)persistent,
                                .end = persistent == _end ? 0 : (uintptr_t)_end,
                                .name = "data" },
                              { .start = 0, .end = 0, .name = NULL },
                          };
                        /*- endif -*/
                        break;
                    }
                /*- endfor -*/

                default:
                    thread_name = "<unknown>";
                    memory_map = NULL;
                    break;
            }

            camkes_show_fault(info, (seL4_CPtr)badge, thread_name,
                /*- if options.fprovide_tcb_caps -*/
                    true,
                /*- else -*/
                    false,
                /*- endif -*/
                memory_map);
        }
    }
/*- endif -*/

int USED main(int argc UNUSED, char *argv[]) {
    assert(argc == 2);
    assert(strcmp(argv[0], "camkes") == 0);

    int thread_id = (int)(argv[1]);

#if defined(SEL4_DEBUG_KERNEL) && defined(CONFIG_CAMKES_PROVIDE_TCB_CAPS)
   /*- set thread_name = c_symbol() -*/
   char /*? thread_name ?*/[seL4_MsgMaxLength * sizeof(seL4_Word)];
   snprintf(/*? thread_name ?*/, sizeof(/*? thread_name ?*/), "%s(%d)",
       get_instance_name(), thread_id);
   /*? thread_name ?*/[sizeof(/*? thread_name ?*/) - 1] = '\0';
   seL4_DebugNameThread(camkes_get_tls()->tcb_cap, /*? thread_name ?*/);
#endif

    /*- if options.fsupport_init -*/
        /*# Locks for synchronising init ops. #*/
        /*- set pre_init_ep = alloc('pre_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set pre_init_lock = c_symbol('pre_init_lock') -*/
        static volatile int UNUSED /*? pre_init_lock ?*/ = 0;
        /*- set interface_init_ep = alloc('interface_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set interface_init_lock = c_symbol('interface_init_lock') -*/
        static volatile int UNUSED /*? interface_init_lock ?*/ = 0;
        /*- set post_init_ep = alloc('post_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set post_init_lock = c_symbol('post_init_lock') -*/
        static volatile int UNUSED /*? post_init_lock ?*/ = 0;
    /*- endif -*/

    switch (thread_id) {

        case 0:
            /* This case is just here to help debugging. If you hit this case,
             * what is happening is probably a failure in passing arguments
             * (thread ID) from our loader.
             */
            assert(!"invalid thread ID");
            return -1;

        /*- set tcb_control = alloc('%d_0_control_%d_tcb' % (len(me.name), len('0_control')), seL4_TCBObject) -*/
        case /*? tcb_control ?*/ : /* Control thread */
            /*? init ?*/();
            /*- if options.fsupport_init -*/
                if (pre_init) {
                    pre_init();
                }
                /* Wake all the interface threads. */
                /*- for _ in threads[1:] -*/
                    sync_sem_bare_post(/*? pre_init_ep ?*/, &/*? pre_init_lock ?*/);
                /*- endfor -*/
                /* wait for all the interface threads to run their inits. */
                /*- for _ in threads[1:] -*/
                    sync_sem_bare_wait(/*? interface_init_ep ?*/, &/*? interface_init_lock ?*/);
                /*- endfor -*/
                if (post_init) {
                    post_init();
                }
                /* Wake all the interface threads. */
                /*- for _ in threads[1:] -*/
                    sync_sem_bare_post(/*? post_init_ep ?*/, &/*? post_init_lock ?*/);
                /*- endfor -*/
            /*- endif -*/
            /*- if me.type.control -*/
                return run();
            /*- else -*/
                return 0;
            /*- endif -*/

        /*# Interface threads #*/
        /*- for t in threads[1:] -*/
            /*- set tcb = alloc('%d_%s_%d_%04d_tcb' % (len(me.name), t.interface.name, len(t.interface.name), t.intra_index), seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Interface /*? t.interface.name ?*/ */
                /*- if options.fsupport_init -*/
                    /* Wait for `pre_init` to complete. */
                    sync_sem_bare_wait(/*? pre_init_ep ?*/, &/*? pre_init_lock ?*/);
                    if (/*? t.interface.name ?*/__init) {
                        /*? t.interface.name ?*/__init();
                    }
                    /* Notify the control thread that we've completed init. */
                    sync_sem_bare_post(/*? interface_init_ep ?*/, &/*? interface_init_lock ?*/);
                    /* Wait for the `post_init` to complete. */
                    sync_sem_bare_wait(/*? post_init_ep ?*/, &/*? post_init_lock ?*/);
                /*- endif -*/
                extern int /*? t.interface.name ?*/__run(void) WEAK;
                if (/*? t.interface.name ?*/__run) {
                    return /*? t.interface.name ?*/__run();
                } else {
                    /* Interface not connected. */
                    return 0;
                }
            }
        /*- endfor -*/

        /*- if options.debug_fault_handlers -*/
            /*- set tcb = alloc('%d_0_fault_handler_%d_0000_tcb' % (len(me.name), len('0_fault_handler')), seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Fault handler thread */
                /*? fault_handler ?*/();
                UNREACHABLE();
                return 0;
            }
        /*- endif -*/

        default:
            /* If we reach this point, the initialiser gave us a thread we
             * weren't expecting.
             */
            assert(!"Template generation failure");
            return -1;
    }
}

/*- for e in me.type.emits -*/
    void /*? e.name ?*/_emit_underlying(void) WEAK;
    void /*? e.name ?*/_emit(void) {
        /* If the interface is not connected, the 'underlying' function will
         * not exist.
         */
        if (/*? e.name ?*/_emit_underlying) {
            /*? e.name ?*/_emit_underlying();
        }
    }
/*- endfor -*/

/* Prototypes for functions generated in per-interface files. */
/*- for d in me.type.dataports -*/
    extern int /*? d.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr)
    /*- if d.optional -*/
        WEAK
    /*- endif -*/
    ;
/*- endfor -*/
dataport_ptr_t dataport_wrap_ptr(void *ptr UNUSED) {
    dataport_ptr_t p = { .id = -1 };
    /*- for d in me.type.dataports -*/
        if (
            /*- if d.optional -*/
                /*? d.name ?*/_wrap_ptr != NULL &&
            /*- endif -*/
            /*? d.name ?*/_wrap_ptr(&p, ptr) == 0) {
            return p;
        }
    /*- endfor -*/
    return p;
}

/* Prototypes for functions generated in per-interface files. */
/*- for d in me.type.dataports -*/
    extern void * /*? d.name ?*/_unwrap_ptr(dataport_ptr_t *p)
    /*- if d.optional -*/
        WEAK
    /*- endif -*/
    ;
/*- endfor -*/
void *dataport_unwrap_ptr(dataport_ptr_t p UNUSED) {
    void *ptr = NULL;
    /*- for d in me.type.dataports -*/
        /*- if d.optional -*/
            if (/*? d.name ?*/_unwrap_ptr != NULL) {
        /*- endif -*/
                ptr = /*? d.name ?*/_unwrap_ptr(&p);
                if (ptr != NULL) {
                    return ptr;
                }
        /*- if d.optional -*/
            }
        /*- endif -*/
    /*- endfor -*/
    return ptr;
}
