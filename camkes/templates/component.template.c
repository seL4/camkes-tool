/*#
 *# Copyright 2014, NICTA
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
#include <camkes/io.h>
#include <camkes/tls.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
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
/*- set dma_pool = configuration[me.name].get('dma_pool', 0) -*/

/*- set p = Perspective() -*/
static char /*? p['dma_pool_symbol'] ?*/[ROUND_UP_UNSAFE(/*? dma_pool ?*/, PAGE_SIZE_4K)]
    __attribute__((section("persistent")))
    __attribute__((aligned(PAGE_SIZE_4K)));

/*- set get_paddr = c_symbol('get_paddr') -*/
uintptr_t /*? get_paddr ?*/(void *ptr) {
    uintptr_t base UNUSED = (uintptr_t)ptr & ~MASK(PAGE_BITS_4K);
    uintptr_t offset UNUSED = (uintptr_t)ptr & MASK(PAGE_BITS_4K);
    /*- for i in range(int(ROUND_UP(dma_pool, PAGE_SIZE) / PAGE_SIZE)) -*/
        /*- if not loop.first -*/
            else
        /*- endif -*/
        if (base == (uintptr_t)/*? p['dma_pool_symbol'] ?*/ + /*? i ?*/ * PAGE_SIZE_4K) {
            /*- set p = Perspective(dma_frame_index=i) -*/
            /*- set frame = alloc(p['dma_frame_symbol'], seL4_FrameObject) -*/
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
void *camkes_io_map(void *cookie UNUSED, uintptr_t paddr, size_t size,
        int cached UNUSED, ps_mem_flags_t flags UNUSED) {

    /*- for d in me.type.dataports -*/
        extern void * /*? d.name ?*/_translate_paddr(uintptr_t paddr,
            size_t size) __attribute__((weak));
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
int camkes_io_port_in(void *cookie UNUSED, uint32_t port, int io_size,
    uint32_t *result) {
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
int camkes_io_port_out(void *cookie UNUSED, uint32_t port, int io_size,
        uint32_t val) {
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
    /*- set aep = alloc(m.name, seL4_AsyncEndpointObject, read=True, write=True) -*/
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
    int res = camkes_dma_init(/*? p['dma_pool_symbol'] ?*/,
        ROUND_UP(/*? dma_pool ?*/, PAGE_SIZE_4K), PAGE_SIZE_4K,
        /*? get_paddr ?*/);
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
    /*- for i in range(tcb_pool) -*/
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
    /*- for i in range(ep_pool) -*/
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
    /*- for i in range(aep_pool) -*/
        /*- set aep = alloc('aep_pool_%d' % i, seL4_AsyncEndpointObject, read=True, write=True) -*/
        res = camkes_provide(seL4_AsyncEndpointObject, /*? aep ?*/, 0, seL4_CanRead|seL4_CanWrite);
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "failed to add AEP /*? aep + 1 ?*/ to cap allocation pool",
            }), ({
                return;
            }));
    /*- endfor -*/
    /*- set untyped_pool = [] -*/
    /*- if configuration is not none -*/
        /*- for attribute, value in configuration[me.name].items() -*/
            /*- set r = re.match('untyped(\\d+)_pool', attribute) -*/
            /*- if r is not none -*/
                /*- do untyped_pool.append((r.group(1), value)) -*/
            /*- endif -*/
        /*- endfor -*/
    /*- endif -*/
    /*- for u in untyped_pool -*/
        /*- for i in range(u[1]) -*/
            /*- if not 4 <= int(u[0]) <= 28 -*/
                /*? raise(Exception('illegal untyped size')) ?*/
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

/*- set all_interfaces = me.type.provides + me.type.uses + me.type.emits + me.type.consumes + me.type.dataports -*/
/*- for i in all_interfaces -*/
    /*? macros.show_includes(i.type.includes, '../static/components/' + me.type.name + '/') ?*/
/*- endfor -*/

/* Thread stacks */
/*- set p = Perspective(instance=me.name, control=True) -*/
/*- set stack_size = configuration[me.name].get('_control_stack_size', 'CONFIG_CAMKES_DEFAULT_STACK_SIZE') -*/
/*? macros.thread_stack(p['stack_symbol'], stack_size) ?*/
/*- for i in all_interfaces -*/
    /*- set p = Perspective(instance=me.name, interface=i.name) -*/
    /*- set stack_size = configuration[me.name].get('%s_stack_size' % i.name, 'CONFIG_CAMKES_DEFAULT_STACK_SIZE') -*/
    /*? macros.thread_stack(p['stack_symbol'], stack_size) ?*/
/*- endfor -*/

/* IPC buffers */
/*- set p = Perspective(instance=me.name, control=True) -*/
/*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- for i in all_interfaces -*/
    /*- set p = Perspective(instance=me.name, interface=i.name) -*/
    /*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- endfor -*/

/*- if configuration is not none -*/
    /* Attributes */
    /*- set myconf = configuration[me.name] -*/
    /*- for a in me.type.attributes -*/
        /*- set value = myconf.get(a.name) -*/
        /*- if value is not none -*/
            const /*? show(a.type) ?*/ /*? a.name ?*/ = /*? value ?*/;
        /*- endif -*/
    /*- endfor -*/
/*- endif -*/

/*- set p = Perspective(instance=me.name) -*/
void USED /*? p['tls_symbol'] ?*/(int thread_id) {
    switch (thread_id) {
        /*- set tcb_control = alloc('tcb__control', seL4_TCBObject) -*/
        case /*? tcb_control ?*/ : /* Control thread */
            /*- set p = Perspective(instance=me.name, control=True) -*/
            /*? macros.save_ipc_buffer_address(p['ipc_buffer_symbol']) ?*/
            camkes_get_tls()->tcb_cap = /*? tcb_control ?*/;
            camkes_get_tls()->thread_index = 1;
            break;

        /*# Interface threads #*/
        /*- for index, i in enumerate(all_interfaces) -*/
            /*- set tcb = alloc('tcb_%s' % i.name, seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Interface /*? i.name ?*/ */
                /*- set p = Perspective(instance=me.name, interface=i.name) -*/
                /*? macros.save_ipc_buffer_address(p['ipc_buffer_symbol']) ?*/
                camkes_get_tls()->tcb_cap = /*? tcb ?*/;
                camkes_get_tls()->thread_index = /*? index ?*/ + 2;
                break;
            }
        /*- endfor -*/
        default:
            assert(!"invalid thread ID");
    }
}

/*- set p = Perspective(instance=me.name) -*/
int USED /*? p['entry_symbol'] ?*/(int thread_id) {

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

        /*- set tcb_control = alloc('tcb__control', seL4_TCBObject) -*/
        case /*? tcb_control ?*/ : /* Control thread */
            /*? init ?*/();
            /*- if options.fsupport_init -*/
                if (pre_init) {
                    pre_init();
                }
                /* Wake all the interface threads. */
                /*- for i in all_interfaces -*/
                    sync_sem_bare_post(/*? pre_init_ep ?*/, &/*? pre_init_lock ?*/);
                /*- endfor -*/
                /* wait for all the interface threads to run their inits. */
                /*- for i in all_interfaces -*/
                    sync_sem_bare_wait(/*? interface_init_ep ?*/, &/*? interface_init_lock ?*/);
                /*- endfor -*/
                if (post_init) {
                    post_init();
                }
                /* Wake all the interface threads. */
                /*- for i in all_interfaces -*/
                    sync_sem_bare_post(/*? post_init_ep ?*/, &/*? post_init_lock ?*/);
                /*- endfor -*/
            /*- endif -*/
            /*- if me.type.control -*/
                return run();
            /*- else -*/
                return 0;
            /*- endif -*/

        /*# Interface threads #*/
        /*- for index, i in enumerate(all_interfaces) -*/
            /*- set tcb = alloc('tcb_%s' % i.name, seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Interface /*? i.name ?*/ */
                /*- if options.fsupport_init -*/
                    /* Wait for `pre_init` to complete. */
                    sync_sem_bare_wait(/*? pre_init_ep ?*/, &/*? pre_init_lock ?*/);
                    if (/*? i.name ?*/__init) {
                        /*? i.name ?*/__init();
                    }
                    /* Notify the control thread that we've completed init. */
                    sync_sem_bare_post(/*? interface_init_ep ?*/, &/*? interface_init_lock ?*/);
                    /* Wait for the `post_init` to complete. */
                    sync_sem_bare_wait(/*? post_init_ep ?*/, &/*? post_init_lock ?*/);
                /*- endif -*/
                extern int /*? i.name ?*/__run(void) __attribute__((weak));
                if (/*? i.name ?*/__run) {
                    return /*? i.name ?*/__run();
                } else {
                    /* Interface not connected. */
                    return 0;
                }
            }
        /*- endfor -*/

        default:
            /* If we reach this point, the initialiser gave us a thread we
             * weren't expecting.
             */
            assert(!"Template generation failure");
            return -1;
    }
}

/*- for e in me.type.emits -*/
    void /*? e.name ?*/_emit_underlying(void) __attribute__((weak));
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
        __attribute__((weak))
    /*- endif -*/
    ;
/*- endfor -*/
dataport_ptr_t dataport_wrap_ptr(void *ptr) {
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
        __attribute__((weak))
    /*- endif -*/
    ;
/*- endfor -*/
void *dataport_unwrap_ptr(dataport_ptr_t p) {
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
