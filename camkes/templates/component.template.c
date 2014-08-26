/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*- import 'macros.jinja' as macros -*/

#include <autoconf.h>
#include <assert.h>
#include <sel4/types.h>
#include <sel4/sel4.h>
/*- if len(me.type.mutexes) > 0 -*/
    #include <sync/mutex.h>
/*- endif -*/
/*- if len(me.type.semaphores) > 0 -*/
    #include <sync/sem.h>
/*- endif -*/
#include <sel4platsupport/platsupport.h>
#include <camkes/allocator.h>
#include <camkes/dataport.h>
#include <camkes/tls.h>
#include <stdlib.h>
#include <sync/sem-bare.h>
#include <sel4debug/identity.h>
#include <utils/util.h>

/*# Include path based on logic in the Makefile template. #*/
/* Include the generated per-component header. */
#include "../../../include//*? me.name ?*//generated//*? me.type.name ?*/.h"

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
    /*- if configuration -*/
        /*- set count = filter(lambda('x: x.instance == \'%s\' and x.attribute == \'%s_value\'' % (me.name, s.name)),  configuration.settings) -*/
        /*- if len(count) > 0 -*/
            /*? count[0].value ?*/
        /*- else -*/
            1
        /*- endif -*/
    /*- else -*/
        1
    /*- endif -*/
    );
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

/* General CAmkES platform initialisation. Expects to be run in a
 * single-threaded, exclusive context. On failure it does not return.
 */
/*- set init = c_symbol() -*/
static void /*? init ?*/(void) {
    int UNUSED res;
    debug_set_id_fn(get_instance_name);
    /*- for m in me.type.mutexes -*/
        res = mutex_/*? m.name ?*/_init();
        if (res != 0) {
            assert(!"initialisation of mutex \"/*? m.name ?*/\" failed");
            abort();
        }
    /*- endfor -*/
    /*- for s in me.type.semaphores -*/
        res = semaphore_/*? s.name ?*/_init();
        if (res != 0) {
            assert(!"initialisation of semaphore \"/*? s.name ?*/\" failed");
            abort();
        }
    /*- endfor -*/

    /* Initialise cap allocator. */
    /*- set tcb_pool = [] -*/
    /*- set ep_pool = [] -*/
    /*- set aep_pool = [] -*/
    /*- set untyped_pool = [] -*/
    /*- if configuration -*/
        /*- for s in configuration.settings -*/
            /*- if s.instance == me.name -*/
                /*- set r = re.match('untyped([0-9]+)_pool', s.attribute) -*/
                /*- if s.attribute == 'tcb_pool' -*/
                    /*- do tcb_pool.append(s.value) -*/
                /*- elif s.attribute == 'ep_pool' -*/
                    /*- do ep_pool.append(s.value) -*/
                /*- elif s.attribute == 'aep_pool' -*/
                    /*- do aep_pool.append(s.value) -*/
                /*- elif r -*/
                    /*- do untyped_pool.append((r.group(1), s.value)) -*/
                /*- endif -*/
            /*- endif -*/
        /*- endfor -*/
    /*- endif -*/
    /*- if tcb_pool -*/
        /*- for i in range(tcb_pool[0]) -*/
            /*- set tcb = alloc('tcb_pool_%d' % i, seL4_TCBObject, read=True, write=True) -*/
            res = camkes_provide(seL4_TCBObject, /*? tcb ?*/, 0, seL4_CanRead|seL4_CanWrite);
            if (res != 0) {
                assert(!"failed to add TCB /*? tcb + 1 ?*/ to cap allocation pool");
                abort();
            }
        /*- endfor -*/
    /*- endif -*/
    /*- if ep_pool -*/
        /*- for i in range(ep_pool[0]) -*/
            /*- set ep = alloc('ep_pool_%d' % i, seL4_EndpointObject, read=True, write=True) -*/
            res = camkes_provide(seL4_EndpointObject, /*? ep ?*/, 0, seL4_CanRead|seL4_CanWrite);
            if (res != 0) {
                assert(!"failed to add EP /*? ep + 1 ?*/ to cap allocation pool");
                abort();
            }
        /*- endfor -*/
    /*- endif -*/
    /*- if aep_pool -*/
        /*- for i in range(aep_pool[0]) -*/
            /*- set aep = alloc('aep_pool_%d' % i, seL4_AsyncEndpointObject, read=True, write=True) -*/
            res = camkes_provide(seL4_AsyncEndpointObject, /*? aep ?*/, 0, seL4_CanRead|seL4_CanWrite);
            if (res != 0) {
                assert(!"failed to add AEP /*? aep + 1 ?*/ to cap allocation pool");
                abort();
            }
        /*- endfor -*/
    /*- endif -*/
    /*- for u in untyped_pool -*/
        /*- for i in range(u[1]) -*/
            /*- if int(u[0]) > 28 or int(u[0]) < 4 -*/
                /*? raise(Exception('illegal untyped size')) ?*/
            /*- endif -*/
            /*- set untyped = alloc('untyped_%s_pool_%d' % (u[0], i), seL4_UntypedObject, size_bits=int(u[0]), read=True, write=True) -*/
            res = camkes_provide(seL4_UntypedObject, /*? untyped ?*/, 1U << /*? u[0] ?*/, seL4_CanRead|seL4_CanWrite);
            if (res != 0) {
                assert(!"failed to add untyped /*? untyped + 1 ?*/ of size /*? u[0] ?*/ bits to cap allocation pool");
                abort();
            }
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
/*? macros.thread_stack(p['stack_symbol']) ?*/
/*- for i in all_interfaces -*/
    /*- set p = Perspective(instance=me.name, interface=i.name) -*/
    /*? macros.thread_stack(p['stack_symbol']) ?*/
/*- endfor -*/

/* IPC buffers */
/*- set p = Perspective(instance=me.name, control=True) -*/
/*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- for i in all_interfaces -*/
    /*- set p = Perspective(instance=me.name, interface=i.name) -*/
    /*? macros.ipc_buffer(p['ipc_buffer_symbol']) ?*/
/*- endfor -*/

/*- if configuration -*/
    /* Attributes */
    /*- for s in configuration.settings -*/
        /*- if s.instance == me.name -*/
            /*# This attribute is for this component instance; now locate it. #*/
            /*- for a in me.type.attributes -*/
                /*- if a.name == s.attribute -*/
                    const /*? show(a.type) ?*/ /*? a.name ?*/ = /*? s.value ?*/;
                /*- endif -*/
            /*- endfor -*/
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
            assert(!"Unreachable");
    }
}

/*- set p = Perspective(instance=me.name) -*/
int USED /*? p['entry_symbol'] ?*/(int thread_id) {

    /*- if options.fsupport_init -*/
        /*# Locks for synchronising init ops. #*/
        /*- set pre_init_ep = alloc('pre_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set pre_init_lock = c_symbol('pre_init_lock') -*/
        static volatile int __attribute__((unused)) /*? pre_init_lock ?*/ = 0;
        /*- set interface_init_ep = alloc('interface_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set interface_init_lock = c_symbol('interface_init_lock') -*/
        static volatile int __attribute__((unused)) /*? interface_init_lock ?*/ = 0;
        /*- set post_init_ep = alloc('post_init_ep', seL4_EndpointObject, read=True, write=True) -*/
        /*- set post_init_lock = c_symbol('post_init_lock') -*/
        static volatile int __attribute__((unused)) /*? post_init_lock ?*/ = 0;
    /*- endif -*/

    switch (thread_id) {

        case 0:
            /* This case is just here to help debugging. If you hit this case,
             * what is happening is probably a failure in passing arguments
             * (thread ID) from our loader.
             */
            assert(!"Unreachable");
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

/*# We need to emit dataports here, rather than in the relevant connection
 *# templates because the dataport may be unconnected, in which case the
 *# connection template will never be invoked.
 #*/
#define MMIO_ALIGN (1 << 12)
/*- for d in me.type.dataports -*/
    /*- set p = Perspective(dataport=d.name) -*/
    char /*? p['dataport_symbol'] ?*/[ROUND_UP_UNSAFE(sizeof(/*? show(d.type) ?*/), PAGE_SIZE_4K)]
        __attribute__((aligned(MMIO_ALIGN)))
        __attribute__((externally_visible));
    volatile /*? show(d.type) ?*/ * /*? d.name ?*/ = (volatile /*? show(d.type) ?*/ *) /*? p['dataport_symbol'] ?*/;
/*- endfor -*/

/* Prototypes for functions generated in per-interface files. */
/*- for d in me.type.dataports -*/
    int /*? d.name ?*/_wrap_ptr(dataport_ptr_t *p, void *ptr)
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
    void * /*? d.name ?*/_unwrap_ptr(dataport_ptr_t *p)
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
