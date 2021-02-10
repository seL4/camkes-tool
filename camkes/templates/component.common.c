/*#
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 #*/

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <sel4runtime/gen_config.h>
#include <assert.h>
#include <camkes.h> /* generated header */
#include <platsupport/io.h>
#include <sel4/types.h>
#include <sel4/sel4.h>
#include <sync/mutex.h>
#include <sync/sem.h>
#include <sync/bin_sem.h>
#include <sel4platsupport/platsupport.h>
#include <camkes/allocator.h>
#include <camkes/dataport.h>
#include <camkes/dma.h>
#include <camkes/error.h>
#include <camkes/fault.h>
#include <camkes/io.h>
#include <camkes/init.h>
#include <camkes/pid.h>
#include <camkes/tls.h>
#include <camkes/vma.h>
#include <camkes/syscalls.h>
#include <sel4runtime.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sync/sem-bare.h>
#include <sel4utils/mapping.h>
#include <sys/types.h>
#include <unistd.h>
#include <utils/util.h>
#include <arch_stdio.h>

/*? macros.show_includes(me.type.includes) ?*/

static void (* _putchar)(int c);

void set_putchar(void (*putchar)(int c)) {
    _putchar = putchar;
}

static
void __camkes_putchar(int c) {
    if (_putchar != NULL) {
        _putchar(c);
        return;
    }
#ifdef CONFIG_PRINTING
    seL4_DebugPutChar(c);
#endif
}

static size_t
write_buf(void *data, size_t count)
{
    char* buf = data;
    for (int i = 0; i < count; i++) {
        __camkes_putchar(buf[i]);
    }
    return count;
}

const char *get_instance_name(void) {
    static const char name[] = "/*? me.name ?*/";
    return name;
}

/*- set cnode_size = configuration[me.address_space].get('cnode_size_bits') -*/
/*- if cnode_size -*/
        /*- if isinstance(cnode_size, six.string_types) -*/
            /*- set size = int(cnode_size, 0) -*/
        /*- else -*/
            /*- set size = cnode_size -*/
        /*- endif -*/
    /*- do my_cnode.__setattr__('size_bits', size) -*/
/*- endif -*/

/* DTB passthrough */


/*# See if this component uses the DTB #*/
/*- set dtb_dict = [] -*/
/*- if configuration[me.name].get('dtb') -*/ /*# Account for the top level .camkes file case, i.e. app #*/
    /*- do dtb_dict.append(configuration[me.name].get('dtb')) -*/
/*- else -*/ /*# Account for the nested .camkes files, i.e. SerialServer/TimeServer #*/
    /*# Check the interfaces and see if the flag is turned on,
     *# this assumes that the interfaces that will turn on the flag
     *# is connected with a variant of the DTB connectors
     #*/
    /*- if me.type.composition -*/
        /*- for c in me.type.composition.connections -*/
            /*- set interface_name = c.to_end.interface.name -*/
            /*- set interface_config_key = '%s.%s' % (me.name, interface_name) -*/
            /*- if configuration.get(interface_config_key) -*/
                /*- if configuration[interface_config_key].get('dtb') -*/
                    /*- do dtb_dict.append(configuration[interface_config_key].get('dtb')) -*/
                    /*- break -*/
                /*- endif -*/
            /*- endif -*/
        /*- endfor -*/
    /*- endif -*/
/*- endif -*/

/*# Output flags to get the loader to copy the DTB over #*/
/*- if len(dtb_dict) -*/
    /*- set dtb_size = dtb_dict[0]['dtb_size'][0] -*/
    /*# Calculate the multiple of 4K pages that can fit the DTB, add an extra for the bootinfo header #*/
    /*- set rounded_size = macros.ROUND_UP(dtb_size, 4096) + 4096 -*/
    char dtb_symbol[/*? rounded_size ?*/]
    ALIGN(PAGE_SIZE_4K) SECTION("align_12bit");
    /*- do register_fill_frame('dtb_symbol', 'CDL_FrameFill_BootInfo CDL_FrameFill_BootInfo_FDT', rounded_size) -*/
/*- endif -*/

/* DMA functionality. */

/*# Determine the size of the DMA pool. Note that we make no attempt to
 *# suppress this attribute being generated as a user-accessible variable at
 *# the top of this file. If the component actually has a declared attribute
 *# 'dma_pool' then they will get access to this variable at runtime.
 #*/
/*- set dma_pool = macros.ROUND_UP(configuration[me.name].get('dma_pool', 0), macros.PAGE_SIZE) -*/
/*- set dma_pool_cache = configuration[me.name].get('dma_pool_cached', False) -*/
/*- set dma_pool_paddr = configuration[me.name].get('dma_pool_paddr', None) -*/
/*- set page_size = [macros.PAGE_SIZE] -*/
/*- if options.largeframe_dma -*/
  /*- for sz in reversed(macros.page_sizes(options.architecture)) -*/
    /*- if dma_pool >= sz -*/
      /*- do page_size.__setitem__(0, sz) -*/
      /*- break -*/
    /*- endif -*/
  /*- endfor -*/
/*- endif -*/

/*- set dma_symbol_name = "%s_dma_pool_symbol" % me.name.replace('.', '_') -*/
char /*? dma_symbol_name ?*/[/*? dma_pool ?*/]
    /*- set page_size_bits = int(math.log(page_size[0], 2)) -*/
    SECTION("align_/*? page_size_bits ?*/bit")
    ALIGN(/*? page_size[0] ?*/);

/*- set dma_frames = [] -*/
/*- set num_dma_frames = int(macros.ROUND_UP(dma_pool, page_size[0]) // page_size[0]) -*/

/*- set dma_frames = [] -*/
/*? register_shared_variable('%s_dma' % me.name, dma_symbol_name , num_dma_frames*page_size[0], frame_size=page_size[0], label=me.label(), perm='RW', cached=dma_pool_cache, with_mapping_caps=dma_frames, paddr=dma_pool_paddr) ?*/

/*# Expose the frames backing the DMA pool #*/
/*- for cap in dma_frames -*/
    static dma_frame_t /*? me.instance.name ?*/_dma_/*? loop.index0 ?*/ = {
        .cap = /*? cap ?*/,
        .size = /*? page_size[0] ?*/,
        .vaddr = (uintptr_t) &/*? dma_symbol_name ?*/[/*? loop.index0 * page_size[0] ?*/],
        .cached = /*? int(dma_pool_cache) ?*/,
    };
/*- endfor -*/

/*- set sanitized_name = me.instance.name.replace('.', '_') -*/

static dma_frame_t */*? sanitized_name ?*/_dma_frames[] = {
    /*- for cap in dma_frames -*/
        &/*? sanitized_name ?*/_dma_/*? loop.index0 ?*/,
    /*- endfor -*/
};

static dma_pool_t /*? sanitized_name ?*/_component_dma_pool = {
    .start_vaddr = (uintptr_t) &/*? dma_symbol_name ?*/[0],
    .end_vaddr = (uintptr_t) &/*? dma_symbol_name ?*/[0] + /*? page_size[0] * num_dma_frames ?*/ - 1,
    .frame_size = /*? page_size[0] ?*/,
    .pool_size = /*? page_size[0] * num_dma_frames ?*/,
    .num_frames = /*? len(dma_frames) ?*/,
    .dma_frames = /*? sanitized_name ?*/_dma_frames,
};
USED SECTION("_dma_pools")
dma_pool_t */*? sanitized_name ?*/_dma_pool_ptr = &/*? sanitized_name ?*/_component_dma_pool;

/* Mutex functionality. */
/*- for m in me.type.mutexes -*/

/*- set mutex = c_symbol(m.name) -*/
static sync_mutex_t /*? mutex ?*/;

static int mutex_/*? m.name ?*/_init(void) {
    /*- set notification = alloc(m.name, seL4_NotificationObject, read=True, write=True) -*/
    return sync_mutex_init(&/*? mutex ?*/, /*? notification ?*/);
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
#ifndef CONFIG_KERNEL_MCS
    camkes_protect_reply_cap();
#endif
    return sync_sem_wait(&/*? semaphore ?*/);
}

int /*? s.name ?*/_trywait(void) {
    return sync_sem_trywait(&/*? semaphore ?*/);
}

int /*? s.name ?*/_post(void) {
    return sync_sem_post(&/*? semaphore ?*/);
}

/*- endfor -*/

/*- for b in me.type.binary_semaphores -*/

/*- set binary_semaphore = c_symbol(b.name) -*/
static sync_bin_sem_t /*? binary_semaphore ?*/;

static int binary_semaphore_/*? b.name ?*/_init(void) {
    /*- set notification = alloc(b.name, seL4_NotificationObject, read=True, write=True) -*/
    /*- set initial = configuration[me.name].get('%s_value' % b.name, 0) -*/
    /*? assert(initial in (0, 1), "Expected 0 or 1 as initial value for binary semaphore \"%s\". Got %d." % (b.name, initial)) ?*/
    return sync_bin_sem_init(&/*? binary_semaphore ?*/, /*? notification ?*/, /*? initial ?*/);
}

int /*? b.name ?*/_wait(void) {
    return sync_bin_sem_wait(&/*? binary_semaphore ?*/);
}

int /*? b.name ?*/_post(void) {
    return sync_bin_sem_post(&/*? binary_semaphore ?*/);
}

/*- endfor -*/

#ifdef CONFIG_CAMKES_DEFAULT_HEAP_SIZE
/*- set heap_size = configuration[me.name].get('heap_size', 'CONFIG_CAMKES_DEFAULT_HEAP_SIZE') -*/

static char heap [/*? heap_size ?*/];
extern char *morecore_area;
extern size_t morecore_size;
#else
/*- if configuration[me.name].get('heap_size') is not none -*/
    #error Set a custom heap_size for component '/*? me.name ?*/' but this has no effect if CONFIG_LIB_SEL4_MUSLC_SYS_MORECORE_BYTES is not set to 0
/*- endif -*/
#endif

/* Install additional syscalls in an init constructor instead of in
 * init so that there is a way for other applications to decide whether
 * they want to provide their syscall implementation before or after
 * the camkes ones */
static void CONSTRUCTOR(CAMKES_SYSCALL_CONSTRUCTOR_PRIORITY) init_install_syscalls(void) {
    camkes_install_syscalls();
}

/* General CAmkES platform initialisation. Expects to be run in a
 * single-threaded, exclusive context. On failure it does not return.
 */
static void CONSTRUCTOR(CAMKES_SYSCALL_CONSTRUCTOR_PRIORITY+1) init(void) {
#ifdef CONFIG_CAMKES_DEFAULT_HEAP_SIZE
    /* Assign the heap */
    morecore_area = heap;
    morecore_size = /*? heap_size ?*/;
#endif

    /* The user has actually had no opportunity to install any error handlers at
     * this point, so any error triggered below will certainly be fatal.
     */
    int res = camkes_dma_init(/*? dma_symbol_name ?*/, /*? dma_pool ?*/,
        /*? page_size[0] ?*/, /*? int(dma_pool_cache) ?*/);
    ERR_IF(res != 0, camkes_error, ((camkes_error_t){
            .type = CE_ALLOCATION_FAILURE,
            .instance = "/*? me.name ?*/",
            .description = "DMA initialisation failed",
        }), ({
            return;
        }));
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
    /*- for b in me.type.binary_semaphores -*/
        res = binary_semaphore_/*? b.name ?*/_init();
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "initialisation of binary semaphore \"/*? b.name ?*/\" failed",
            }), ({
                return;
            }));
    /*- endfor -*/

    /* Initialise cap allocator. */
    /*- set tcb_pool = configuration[me.name].get('tcb_pool', 0) -*/
    /*- for i in six.moves.range(tcb_pool) -*/
        /*- set _tcb = alloc_obj('tcb_pool_%d' % i, seL4_TCBObject) -*/
        /*- set tcb = alloc_cap('tcb_pool_%d' % i, _tcb) -*/
        /*- do _tcb.__setattr__('resume', false) -*/
        /*- if "tcb_pool_domains" in configuration[me.name] -*/
            /*- do _tcb.__setattr__('domain', configuration[me.name].get('tcb_pool_domains')[i]) -*/
        /*- endif -*/
        res = camkes_provide(seL4_TCBObject, /*? tcb ?*/, 0, 0);
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
    /*- set notification_pool = configuration[me.name].get('notification_pool', 0) -*/
    /*- for i in six.moves.range(notification_pool) -*/
        /*- set notification = alloc('notification_pool_%d' % i, seL4_NotificationObject, read=True, write=True) -*/
        res = camkes_provide(seL4_NotificationObject, /*? notification ?*/, 0, seL4_CanRead.words[0]|seL4_CanWrite.words[0]);
        ERR_IF(res != 0, camkes_error, ((camkes_error_t){
                .type = CE_ALLOCATION_FAILURE,
                .instance = "/*? me.name ?*/",
                .description = "failed to add NOTIFICATION /*? notification + 1 ?*/ to cap allocation pool",
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
            /*- set untyped = alloc('untyped_%s_pool_%d' % (u[0], i), seL4_UntypedObject, size_bits=int(u[0])) -*/
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

/*- for i in me.type.provides + me.type.uses -*/
    /*? macros.show_includes(i.type.includes) ?*/
/*- endfor -*/

/*- set threads = macros.threads(composition, me, configuration[me.name], options) -*/

/*- if options.debug_fault_handlers -*/
  /*- set fault_ep = alloc_obj('fault_ep', seL4_EndpointObject) -*/
/*- endif -*/

/*- if options.realtime -*/
    /*# SC to use to initialise all passive interfaces of this instance #*/
    /*- set sc_passive_init = alloc('%d_0_control_%d_passive_init_sc' % (len(me.name), len('0_control')), seL4_SchedContextObject) -*/

    /*# Ntfn to use in passive init protocol #*/
    /*- set ntfn_passive_init = alloc('%d_0_control_%d_passive_init_ntfn' % (len(me.name), len('0_control')), seL4_NotificationObject, read=True, write=True) -*/

    /*# Dict mapping thread prefixes to tcb caps #*/
    /*- set passive_tcbs = {} -*/

    /*# Set of Thread objects corresponding to passive threads #*/
    /*- set passive_threads = set() -*/
/*- endif -*/

/*- set thread_names = dict() -*/
/*- for t in threads -*/
    /* Thread stacks */
    /*? macros.thread_stack(t.stack_symbol, t.stack_size) ?*/
    /*- do register_stack_symbol(t.stack_symbol, t.stack_size) -*/

    /* IPC buffers */
    /*? macros.ipc_buffer(t.ipc_symbol) ?*/
    /*- set ipc_frame = alloc_obj('frame_%s' % (t.ipc_symbol), seL4_FrameObject) -*/
    /*- do register_ipc_symbol(t.ipc_symbol, ipc_frame) -*/

    /*- set _tcb = alloc_obj("%s_tcb" % t.name, seL4_TCBObject) -*/
    /*- set tcb = alloc_cap("%s_tcb" % t.name, _tcb) -*/
    /*- do _tcb.__setitem__('ipc_buffer_slot', Cap(ipc_frame, read=True, write=True)) -*/
    /*- do _tcb.__setitem__('vspace', Cap(my_pd)) -*/
    /*- set cnode_cap = Cap(my_cnode) -*/
    /*- do my_cnode.update_guard_size_caps.append(cnode_cap) -*/
    /*- do _tcb.__setitem__('cspace', cnode_cap) -*/

    /*- do _tcb.__setattr__('ip', "get_vaddr(\'%s\')" % ("camkes %s _camkes_start" % me.name) ) -*/
    /*- do _tcb.__setattr__('sp', t.sp) -*/
    /*- do _tcb.__setattr__('addr', t.addr) -*/
    /*- do _tcb.init.append(tcb) -*/

    /*- if options.realtime -*/
        /*- if not t.interface or not configuration[me.name].get("%s_passive" % t.interface.name, False) -*/
            /*- set _sc = alloc_obj("%s_sc" % t.name, seL4_SchedContextObject) -*/
            /*- set sc = alloc_cap("%s_sc" % t.name, _sc) -*/
            /*- do _tcb.__setitem__('sc_slot', Cap(_sc)) -*/
            /*- if loop.first -*/
                /*- do macros.set_sc_properties(_sc, options, configuration[me.name], "_") -*/
            /*- elif options.debug_fault_handlers and loop.last -*/
                /*- do macros.set_sc_properties(_sc, options, configuration[me.name], "fault") -*/
            /*- else -*/
                /*- do macros.set_sc_properties(_sc, options, configuration[me.name], "%s_" % t.interface.name) -*/
            /*- endif -*/
        /*- else -*/
            /*# This branch is for interface threads that are passive #*/
            /*- do passive_tcbs.__setitem__(t.name, tcb) -*/
            /*- do passive_threads.add(t) -*/
        /*- endif -*/
    /*- endif -*/

    /*- if options.debug_fault_handlers and not loop.last -*/
        /*- if not options.realtime -*/
            /*- set fault_ep_cap = alloc_cap('fault_ep_%s' % t.name, fault_ep, read=True, write=True, grantreply=True, badge=tcb) -*/
            /*- do setattr(_tcb, 'fault_ep_slot', fault_ep_cap) -*/
        /*- endif -*/

        /*- if options.realtime -*/
            /*- do _tcb.set_fault_ep_slot(fault_ep=fault_ep.name, badge=tcb) -*/
        /*- endif -*/

    /*- endif -*/

    /*- if loop.first -*/
        /*- do macros.set_tcb_properties(_tcb, options, configuration[me.name], "_") -*/
        /*- do thread_names.__setitem__(tcb, "control") -*/
    /*- elif options.debug_fault_handlers and loop.last -*/
        /*- do thread_names.__setitem__(tcb, "fault_handler") -*/
        /*- do _tcb.__setattr__('prio', 255) -*/
        /*- do _tcb.__setattr__('affinity', options.default_affinity) -*/
        /*- do _tcb.__setattr__('max_prio', options.default_max_priority) -*/

    /*- else -*/
        /*- do thread_names.__setitem__(tcb, t.interface.name) -*/
        /*- do macros.set_tcb_properties(_tcb, options, configuration[me.name], "%s_" % t.interface.name) -*/
    /*- endif -*/


/*- endfor -*/

/* Attributes */
/*- set myconf = configuration[me.name] -*/
/*- for a in me.type.attributes -*/
    /*- set value = myconf.get(a.name) -*/
    /*- if value is not none -*/
        const /*? macros.show_type(a.type) ?*/ /*? a.name ?*//*- if a.array -*/ [/*?len(value)?*/] /*- endif -*/ =
        /*? macros.show_attribute_value(a, value) ?*/
        ;
    /*- endif -*/
/*- endfor -*/

/*- if options.debug_fault_handlers -*/
  /*- set fault_ep = alloc_obj('fault_ep', seL4_EndpointObject) -*/
/*- endif -*/

const char * get_thread_name(int thread_id) {
    switch (thread_id) {
        /*- for id, name in thread_names.items() -*/
        case /*? id ?*/: return "/*?name?*/";
        /*- endfor -*/
    }
    return "(unknown)";
}

static int post_main(int thread_id);
void USED NORETURN _camkes_start_c(int thread_id) {
    /*- set tcb_control = alloc("%s_tcb" % threads[0].name, seL4_TCBObject) -*/
    if (thread_id != /*? tcb_control ?*/) {
        post_main(thread_id);
    } else {
        sel4muslcsys_register_stdio_write_fn(write_buf);
        void *ipc_buf_ptr = (void *) /*? macros.ipc_buffer_address(threads[0].ipc_symbol) ?*/;
        camkes_start_control(thread_id, ipc_buf_ptr);
    }
    UNREACHABLE();
}

// a tls region for every thread except the control thread
static void *tls_regions[/*? len(threads) - 1 ?*/];
// static tls regions
static char static_tls_regions[/*? len(threads) - 1 ?*/][CONFIG_SEL4RUNTIME_STATIC_TLS];

void camkes_tls_init(int thread_id) {
    switch (thread_id) {
        /*- for index, t in enumerate(threads) -*/
            /*- set tcb = alloc('%s_tcb' % t.name, seL4_TCBObject) -*/

            case /*? tcb ?*/ : { /* Thread /*? t.name ?*/ */
                /*- if tcb == tcb_control -*/
                // the control thread has an initial tls region created for it,
                // but this may fail if the tls region is too big.
                ZF_LOGF_IF(!sel4runtime_initial_tls_enabled(), "Failed to init TLS");
                /*- else -*/
                void *tls_mem = tls_regions[/*? loop.index - 2?*/];
                assert(tls_mem != NULL);
                uintptr_t tls_base = sel4runtime_write_tls_image(tls_mem);
                sel4runtime_set_tls_base(tls_base);
                ZF_LOGF_IF(!tls_base, "Failed to write new tls");
                __sel4_ipc_buffer = (seL4_IPCBuffer *) /*? macros.ipc_buffer_address(t.ipc_symbol) ?*/;
                /*- endif -*/
                /*- if options.realtime and loop.first -*/
                    /*- set sc_context = alloc("%s_sc" % t.name, seL4_SchedContextObject) -*/
                    camkes_get_tls()->sc_cap = /*? sc_context ?*/;
                /*- endif -*/
                camkes_get_tls()->tcb_cap = /*? tcb ?*/;
                camkes_get_tls()->thread_index = /*? index ?*/ + 1;
                break;
            }
        /*- endfor -*/

        default:
            assert(!"invalid thread ID");
    }

/*- if options.fprovide_tcb_caps -*/
#ifdef CONFIG_DEBUG_BUILD
   char thread_name[seL4_MsgMaxLength * sizeof(seL4_Word)];
   snprintf(thread_name, sizeof(thread_name), "%s:%s",
       get_instance_name(), get_thread_name(thread_id));
   thread_name[sizeof(thread_name) - 1] = '\0';
   seL4_DebugNameThread(camkes_get_tls()->tcb_cap, thread_name);
#endif
/*- endif -*/
}
/*- if options.debug_fault_handlers -*/
    static void fault_handler(void) UNUSED NORETURN;
    static void fault_handler(void) {
        while (true) {
            seL4_Word badge;

            /* Wait for a fault from one of the component's threads. */
            /*- set fault_ep_cap = alloc_cap('fault_ep__fault_handler', fault_ep, read=True, write=True, grantreply=True) -*/
            /*- if options.realtime -*/
                /*- set fault_reply_cap = alloc('fault_reply__fault_handler', seL4_RTReplyObject) -*/
            /*- endif -*/
            seL4_MessageInfo_t info = /*? generate_seL4_Recv(options, fault_ep_cap, '&badge', fault_reply_cap) ?*/;

            /* Various symbols that are provided by the linker script. */
            extern const char __executable_start[1];
            extern const char align_12bit[1] UNUSED;
            extern const char _end[1] UNUSED;

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

                /*- for t in threads -*/
                    /*- set tcb = alloc('%s_tcb' % t.name, seL4_TCBObject) -*/
                    case /*? tcb ?*/ : {
                        thread_name = "/*? t.name ?*/";
                        memory_map = (camkes_memory_region_t[]){
                            { .start = (uintptr_t)__executable_start,
                              .end = (uintptr_t)align_12bit - 1,
                              .name = "code and data" },
                            { .start = (uintptr_t)&/*? t.stack_symbol ?*/,
                              .end = (uintptr_t)&/*? t.stack_symbol ?*/ + PAGE_SIZE_4K - 1,
                              .name = "guard page" },
                            { .start = (uintptr_t)&/*? t.stack_symbol ?*/ + PAGE_SIZE_4K,
                              .end = (uintptr_t)&/*? t.stack_symbol ?*/ +
                                sizeof(/*? t.stack_symbol ?*/) - PAGE_SIZE_4K - 1,
                              .name = "stack" },
                            { .start = (uintptr_t)&/*? t.stack_symbol ?*/ +
                                sizeof(/*? t.stack_symbol ?*/) - PAGE_SIZE_4K,
                              .end = (uintptr_t)&/*? t.stack_symbol ?*/ +
                                sizeof(/*? t.stack_symbol ?*/) - 1,
                              .name = "guard page" },
                            { .start = (uintptr_t)&/*? t.ipc_symbol ?*/,
                              .end = (uintptr_t)&/*? t.ipc_symbol ?*/ + PAGE_SIZE_4K - 1,
                              .name = "guard page" },
                            { .start = (uintptr_t)&/*? t.ipc_symbol ?*/ + PAGE_SIZE_4K,
                              .end = (uintptr_t)&/*? t.ipc_symbol ?*/ +
                                sizeof(/*? t.ipc_symbol ?*/) - PAGE_SIZE_4K - 1,
                              .name = "IPC buffer" },
                            { .start = (uintptr_t)&/*? t.ipc_symbol ?*/ +
                                sizeof(/*? t.ipc_symbol ?*/) - PAGE_SIZE_4K,
                              .end = (uintptr_t)&/*? t.ipc_symbol ?*/ +
                                sizeof(/*? t.ipc_symbol ?*/) - 1,
                              .name = "guard page" },
                            { .start = 0, .end = 0, .name = NULL },
                        };
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

/*# Locks for synchronising init ops. These are used by
    pre_init_interface_sync, post_init_interface_sync and post_main
  #*/
/*- set pre_init_ep = alloc('pre_init_ep', seL4_EndpointObject, read=True, write=True) -*/
static volatile int UNUSED pre_init_lock = 0;
/*- set interface_init_ep = alloc('interface_init_ep', seL4_EndpointObject, read=True, write=True) -*/
static volatile int UNUSED interface_init_lock = 0;
/*- set post_init_ep = alloc('post_init_ep', seL4_EndpointObject, read=True, write=True) -*/
static volatile int UNUSED post_init_lock = 0;

int pre_init_interface_sync() {
    int result UNUSED;

    /* Wake all the non-passive interface threads. */
    /*- for t in threads[1:] -*/
        /*- if not options.realtime or t not in passive_threads -*/
            sync_sem_bare_post(/*? pre_init_ep ?*/, &pre_init_lock);
        /*- endif -*/
    /*- endfor -*/

    /* Wait for all the non-passive interface threads to run their inits. */
    /*- for t in threads[1:] -*/
        /*- if not (options.debug_fault_handlers and loop.last) -*/
        /*- if not options.realtime or t not in passive_threads -*/
            sync_sem_bare_wait(/*? interface_init_ep ?*/, &interface_init_lock);
        /*- endif -*/
        /*- endif -*/
    /*- endfor -*/

    /*- if options.realtime -*/
        /* Wake each passive thread one at a time and allow it to run its init. */
        /*- for prefix, tcb in passive_tcbs.items() -*/
            result = seL4_SchedContext_Bind(/*? sc_passive_init ?*/, /*? tcb ?*/);
            ERR_IF(result != 0, camkes_error, ((camkes_error_t){
                    .type = CE_SYSCALL_FAILED,
                    .instance = "/*? me.name ?*/",
                    .description = "failed to bind initialisation scheduling context for thread \"/*? prefix ?*/_tcb\"",
                    .syscall = SchedContextBind,
                    .error = result,
                }), ({
                    return -1;
                }));

            /*# Wake thread #*/
            sync_sem_bare_post(/*? pre_init_ep ?*/, &pre_init_lock);

            /*# Wait for thread to run its init #*/
            sync_sem_bare_wait(/*? interface_init_ep ?*/, &interface_init_lock);

            result = seL4_SchedContext_Unbind(/*? sc_passive_init ?*/);
            ERR_IF(result != 0, camkes_error, ((camkes_error_t){
                    .type = CE_SYSCALL_FAILED,
                    .instance = "/*? me.name ?*/",
                    .description = "failed to unbind initialisation scheduling context for thread \"/*? prefix ?*/_tcb\"",
                    .syscall = SchedContextUnbind,
                    .error = result,
                }), ({
                    return -1;
                }));
        /*- endfor -*/
    /*- endif -*/
    return 0;
}

int post_init_interface_sync() {
    int result UNUSED;

    /* Wake all the interface threads, including passive threads.
     * Passive threads will receive the IPC despite not having scheduling contexts
     * at this point. Next time they are given scheduling contexts they will be
     * unblocked. */
    /*- for _ in threads[1:] -*/
        /*- if not (options.debug_fault_handlers and loop.last) -*/
        sync_sem_bare_post(/*? post_init_ep ?*/, &post_init_lock);
        /*- endif -*/
    /*- endfor -*/

    /*- if options.realtime -*/
        /* Tempororily bind a scheduling context to each passive thread
         * and allow it to start waiting on an endpoint. Threads will
         * indicate that they are ready to have their sc unbound when
         * they send on the init notification. */
        /*- for prefix, tcb in passive_tcbs.items() -*/

            /*# Bind the initialision scheduling context to the tcb. #*/
            result = seL4_SchedContext_Bind(/*? sc_passive_init ?*/, /*? tcb ?*/);
            ERR_IF(result != 0, camkes_error, ((camkes_error_t){
                    .type = CE_SYSCALL_FAILED,
                    .instance = "/*? me.name ?*/",
                    .description = "failed to bind initialisation scheduling context for thread \"/*? prefix ?*/_tcb\"",
                    .syscall = SchedContextBind,
                    .error = result,
                }), ({
                    return -1;
                }));

            /*# Wait until the passive interface is finished initialising. #*/
            seL4_Wait(/*? ntfn_passive_init ?*/, NULL);

            /*# Unbind the sc from the tcb. #*/
            result = seL4_SchedContext_Unbind(/*? sc_passive_init ?*/);
            ERR_IF(result != 0, camkes_error, ((camkes_error_t){
                    .type = CE_SYSCALL_FAILED,
                    .instance = "/*? me.name ?*/",
                    .description = "failed to unbind initialisation scheduling context for thread \"/*? prefix ?*/_tcb\"",
                    .syscall = SchedContextUnbind,
                    .error = result,
                }), ({
                    return -1;
                }));
        /*- endfor -*/
    /*- endif -*/
    return 0;
}

static int post_main(int thread_id) {
    int ret = 0;
    switch (thread_id) {

        case 0:
            /* This case is just here to help debugging. If you hit this case,
             * what is happening is probably a failure in passing arguments
             * (thread ID) from our loader.
             */
            assert(!"invalid thread ID");
            return -1;

        case /*? tcb_control ?*/ : /* Control thread */
            camkes_tls_init(thread_id);
            for (int i = 0; i < /*? len(threads) - 1 ?*/; i++) {
                if (sel4runtime_get_tls_size() < CONFIG_SEL4RUNTIME_STATIC_TLS) {
                    tls_regions[i] = static_tls_regions[i];
                } else {
                    tls_regions[i] = malloc(sel4runtime_get_tls_size());
                    ZF_LOGF_IF(tls_regions[i] == NULL, "Failed to create tls");
                }
            }
            ret = component_control_main();
            sync_sem_bare_wait(/*? interface_init_ep ?*/, &interface_init_lock);
            return ret;

        /*# Interface threads #*/
        /*- for t in threads[1:] -*/
        /*- if options.debug_fault_handlers and loop.last -*/
            /*- set tcb = alloc("%s_tcb" % t.name, seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Fault handler thread */
                sync_sem_bare_wait(/*? pre_init_ep ?*/, &pre_init_lock);
                camkes_tls_init(thread_id);
                fault_handler();
                UNREACHABLE();
                return 0;
            }
        /*- else -*/
            /*- set tcb = alloc("%s_tcb" % t.name, seL4_TCBObject) -*/
            case /*? tcb ?*/ : { /* Interface /*? t.interface.name ?*/ */
                /* Wait for `pre_init` to complete. */
                sync_sem_bare_wait(/*? pre_init_ep ?*/, &pre_init_lock);
                camkes_tls_init(thread_id);
                if (/*? t.interface.name ?*/__init) {
                    /*? t.interface.name ?*/__init();
                }
                /* Notify the control thread that we've completed init. */
                sync_sem_bare_post(/*? interface_init_ep ?*/, &interface_init_lock);
                /* Wait for the `post_init` to complete. */
                sync_sem_bare_wait(/*? post_init_ep ?*/, &post_init_lock);

                /*- set prefix = '%s_%s_%04d' % (me.name, t.interface.name, t.intra_index) -*/
                /*- if options.realtime and prefix in passive_tcbs -*/

                    /*# If this is a passive interface, the __run_passive function must SignalRecv to tell the control
                     *# thread to unbind its sc, and simultaneously start waiting for rpc calls. #*/
                    extern int /*? t.interface.name ?*/__run_passive(seL4_CPtr) WEAK;
                    if (/*? t.interface.name ?*/__run_passive) {
                        ret = /*? t.interface.name ?*/__run_passive(/*? ntfn_passive_init ?*/);
                    } else {
                        /* Inform the main component thread that we're finished initialising */
                        seL4_Signal(/*? ntfn_passive_init ?*/);

                    }
                /*- else -*/
                    extern int /*? t.interface.name ?*/__run(void) WEAK;
                    if (/*? t.interface.name ?*/__run) {
                        ret = /*? t.interface.name ?*/__run();
                    }
                /*- endif -*/
                sync_sem_bare_wait(/*? pre_init_ep ?*/, &pre_init_lock);
                return ret;
            }
        /*- endif -*/
        /*- endfor -*/


        default:
            /* If we reach this point, the initialiser gave us a thread we
             * weren't expecting.
             */
            assert(!"Template generation failure");
            return -1;
    }
}

int USED main(int argc UNUSED, char *argv[]) {
    assert(argc == 2);
    assert(strcmp(argv[0], "camkes") == 0);

    int thread_id = (int)(uintptr_t)(argv[1]);
    post_main(thread_id);
    UNREACHABLE();
    return 0;
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

/* These symbols are provided by the default linker script. */
extern const char __executable_start[1]; /* Start of text section */
extern const char __etext[1]; /* End of text section, start of rodata section */
extern const char __preinit_array_start[1]; /* End of rodata section, start of data section */
extern const char _edata[1]; /* End of data section */
extern const char __bss_start[1]; /* Start of bss section */
extern const char _end[1]; /* End of bss section */

/* See vma.h in libsel4camkes for a description of this array. */
const struct camkes_vma camkes_vmas[] = {
    {
        .start = (void*)__executable_start,
        .end = (void*)__etext,
        .read = true,
        .write = false,
        .execute = true,
        .cached = true,
        .name = ".text",
    },
    {
        .start = (void*)__etext,
        .end = (void*)__preinit_array_start,
        .read = true,
        .write = false,
        .execute = false,
        .cached = true,
        .name = ".rodata",
    },
    {
        .start = (void*)__preinit_array_start,
        .end = (void*)_edata,
        .read = true,
        .write = true,
        .execute = false,
        .cached = true,
        .name = ".data",
    },
    {
        .start = (void*)__bss_start,
        .end = (void*)_end,
        .read = true,
        .write = true,
        .execute = false,
        .cached = true,
        .name = ".bss",
    },
    {
        .start = (void*)/*? dma_symbol_name ?*/,
        .end = (void*)/*? dma_symbol_name ?*/ + sizeof(/*? dma_symbol_name ?*/),
        .read = true,
        .write = true,
        .execute = false,
        .cached = false,
        .name = "DMA pool",
    },
    /*- for t in threads -*/
        {
            .start = (void*)/*? t.stack_symbol ?*/,
            .end = (void*)/*? t.stack_symbol ?*/ + PAGE_SIZE_4K,
            .read = false,
            .write = false,
            .execute = false,
            .cached = true,
            .name = "guard page below /*? t.name ?*/ thread's stack",
        },
        {
            .start = (void*)/*? t.stack_symbol ?*/ + PAGE_SIZE_4K,
            .end = (void*)/*? t.stack_symbol ?*/ + sizeof(/*? t.stack_symbol ?*/) - PAGE_SIZE_4K,
            .read = true,
            .write = true,
            .execute = false,
            .cached = true,
            .name = "/*? t.name ?*/ thread's stack",
        },
        {
            .start = (void*)/*? t.stack_symbol ?*/ + sizeof(/*? t.stack_symbol ?*/) - PAGE_SIZE_4K,
            .end = (void*)/*? t.stack_symbol ?*/ + sizeof(/*? t.stack_symbol ?*/),
            .read = false,
            .end = false,
            .execute = false,
            .cached = true,
            .name = "guard page above /*? t.name ?*/ thread's stack",
        },
        {
            .start = (void*)/*? t.ipc_symbol ?*/,
            .end = (void*)/*? t.ipc_symbol ?*/ + PAGE_SIZE_4K,
            .read = false,
            .write = false,
            .execute = false,
            .cached = true,
            .name = "guard page below /*? t.name ?*/ thread's IPC buffer",
        },
        {
            .start = (void*)/*? t.ipc_symbol ?*/ + PAGE_SIZE_4K,
            .end = (void*)/*? t.ipc_symbol ?*/ + (PAGE_SIZE_4K * 2),
            .read = true,
            .write = true,
            .execute = false,
            .cached = true,
            .name = "/*? t.name ?*/ thread's IPC buffer",
        },
        {
            .start = (void*)/*? t.ipc_symbol ?*/ + (PAGE_SIZE_4K * 2),
            .end = (void*)/*? t.ipc_symbol ?*/ + (PAGE_SIZE_4K * 3),
            .read = false,
            .write = false,
            .execute = false,
            .cached = true,
            .name = "guard page above /*? t.name ?*/ thread's IPC buffer",
        },
    /*- endfor -*/
};

const size_t camkes_vmas_size = sizeof camkes_vmas / sizeof camkes_vmas[0];

/*- for index, i in enumerate(composition.instances) -*/
  /*- if id(i) == id(me) -*/
    /* We consider the CapDL initialiser to have PID 1, so offset to skip over this. */
    const pid_t camkes_pid = (pid_t)/*? index ?*/ + (pid_t)2;
    /*- break -*/
  /*- endif -*/
/*- endfor -*/
