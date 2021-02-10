/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* IO port/device functionality. This is meant for interaction with
 * libplatsupport infrastructure.
 */

#include <assert.h>
#include <libfdt.h>
#include <camkes/dataport.h>
#include <camkes/dma.h>
#include <camkes/io.h>
#include <camkes/interface_registration.h>
#include <camkes/irq.h>
#include <camkes/arch/io.h>
#include <platsupport/io.h>
#include <platsupport/driver_module.h>
#include <stdint.h>
#include <stdlib.h>
#include <utils/util.h>

/* Force the _dataport_frames  section to be created even if no modules are defined. */
static USED SECTION("_dataport_frames") struct {} dummy_dataport_frame;
/* Definitions so that we can find the exposed dataport frames */
extern dataport_frame_t __start__dataport_frames[];
extern dataport_frame_t __stop__dataport_frames[];

typedef struct camkes_defer_token {
    char *device_path;
    ps_driver_init_fn_t init_func;
} camkes_defer_token_t;

/* Basic linked-list implementation. */
typedef struct ll_ {
    void *data;
    struct ll_ *next;
} ll_t;

#ifndef NDEBUG
bool malloc_ops_initialised = false;
static ps_malloc_ops_t io_mapper_malloc_ops = {0};
#endif

static UNUSED int ll_prepend(ps_malloc_ops_t *malloc_ops, ll_t **list, const void *data)
{
    ll_t *node = NULL;
    int error = ps_calloc(malloc_ops, 1, sizeof * node, (void **) &node);
    if (error) {
        return -1;
    }
    node->data = (void *)data;
    node->next = *list;
    *list = node;
    return 0;
}

static UNUSED int ll_append(ps_malloc_ops_t *malloc_ops, ll_t **list, const void *data)
{
    ll_t *node = NULL;
    int error = ps_calloc(malloc_ops, 1, sizeof * node, (void **) &node);
    if (error) {
        return -1;
    }
    node->data = (void *)data;
    node->next = NULL;
    if (*list == NULL) {
        *list = node;
        return 0;
    }
    ll_t *curr = NULL;
    for (curr = *list; curr->next != NULL; curr = curr->next);
    curr->next = node;
    return 0;
}

static UNUSED int ll_remove(ps_malloc_ops_t *malloc_ops, ll_t **list, const void *data)
{
    for (ll_t **l = list; *l != NULL; l = &(*l)->next) {
        if ((*l)->data == data) {
            /* found it */
            ll_t *temp = *l;
            *l = (*l)->next;
            ps_free(malloc_ops, sizeof(*temp), temp);
            return 0;
        }
    }
    return -1;
}

typedef struct {
    ps_malloc_ops_t *malloc_ops;
    ps_io_map_fn_t map;
    ll_t *mapped;
} cookie_t;

/* Debug wrapper for IO map. This function calls the underlying map function
 * and tracks results for the purpose of catching illegal unmapping operations.
 * Note that this function is unused when NDEBUG is defined.
 */
static UNUSED void *io_map(void *cookie, uintptr_t paddr, size_t size,
                           int cached, ps_mem_flags_t flags)
{

    /* Call the real IO map function. */
    cookie_t *c = cookie;
    void *p = c->map(NULL, paddr, size, cached, flags);

    if (p != NULL) {
        /* The IO map function gave us a successful result; track this pointer
         * to lookup during unmapping.
         */
        if (ll_prepend(c->malloc_ops, &c->mapped, p) != 0) {
            LOG_ERROR("failed to track mapped IO pointer %p\n", p);
        }
    }

    return p;
}

static int UNUSED pointer_compare(void *a, void *b)
{
    uintptr_t p = (uintptr_t)a;
    uintptr_t q = (uintptr_t)b;
    if (p > q) {
        return 1;
    } else if (p < q) {
        return -1;
    } else {
        return 0;
    }
}

static void *camkes_io_map(void *cookie UNUSED, uintptr_t paddr,
                           size_t size, int cached UNUSED, ps_mem_flags_t flags UNUSED)
{
    if (paddr % PAGE_SIZE_4K != 0 && size % PAGE_SIZE_4K != 0) {
        ZF_LOGE("paddr or size has incorrect alignment: (%p, 0x%zx)", (void *) paddr, size);
        return NULL;
    }

    /* Given a base paddr and size, we try to find a region of mapped memory that
     * is a superset of the given parameters. */
    size_t size_counter = 0;
    bool counting_frames = false;
    uintptr_t base_vaddr = 0;
    for (dataport_frame_t *frame = __start__dataport_frames;
         frame < __stop__dataport_frames; frame++) {
        if (counting_frames) {
            if (paddr == (frame->paddr - size_counter)) {
                size_counter += frame->size;
            } else {
                /* We've encountered a different region of physical memory that does
                   not match what we want, reset the counters */
                counting_frames = false;
                base_vaddr = 0;
                size_counter = 0;
            }
        } else {
            if (paddr >= frame->paddr && (frame->paddr + frame->size) > paddr) {
                /* We've found the first frame of the mapped region,
                   start counting from here */
                counting_frames = true;
                base_vaddr = frame->vaddr + (paddr - frame->paddr);
                size_counter += (frame->vaddr + frame->size) - base_vaddr;
            }
        }

        if (size_counter >= size) {
            /* We've found all the frames that cover the desired region */
            return (void *)base_vaddr;
        }
    }

    /* Not found. */
    return NULL;
}

/* We never unmap anything. */
static void io_unmap(void *cookie UNUSED, void *vaddr UNUSED, size_t size UNUSED)
{
#ifndef NDEBUG
    cookie_t *c = cookie;
    /* Make sure we previously mapped the pointer the caller gave us. */
    if (ll_remove(c->malloc_ops, &c->mapped, vaddr) != 0) {
        LOG_ERROR("unmapping an IO pointer that was not previously mapped: %p\n",
                  vaddr);
    }
#endif
}

int camkes_io_mapper(ps_io_mapper_t *mapper)
{
    if (mapper == NULL) {
        ZF_LOGE("mapper is NULL");
        return -1;
    }
#ifdef NDEBUG
    mapper->cookie = NULL;
    mapper->io_map_fn = camkes_io_map;
#else
    if (!malloc_ops_initialised) {
        ZF_LOGF_IF(camkes_ps_malloc_ops(&io_mapper_malloc_ops),
                   "Failed to get malloc_ops for DEBUG mode io mapper");
        malloc_ops_initialised = true;
    }
    cookie_t *c = NULL;
    int error = ps_calloc(&io_mapper_malloc_ops, 1, sizeof(*c), (void **) &c);
    if (error) {
        return -1;
    }
    c->malloc_ops = &io_mapper_malloc_ops;
    c->map = camkes_io_map;
    c->mapped = NULL;
    mapper->cookie = c;
    mapper->io_map_fn = io_map;
#endif
    mapper->io_unmap_fn = io_unmap;
    return 0;
}

static int camkes_io_port_in(void *cookie UNUSED, uint32_t port, int io_size, uint32_t *result)
{
    return camkes_arch_io_port_in(port, io_size, result);
}

static int camkes_io_port_out(void *cookie UNUSED, uint32_t port, int io_size, uint32_t val)
{
    return camkes_arch_io_port_out(port, io_size, val);
}

int camkes_io_port_ops(ps_io_port_ops_t *ops)
{
    if (ops == NULL) {
        ZF_LOGE("ops is NULL");
        return -1;
    }
    ops->io_port_in_fn = camkes_io_port_in;
    ops->io_port_out_fn = camkes_io_port_out;
    return 0;
}

int camkes_ps_malloc_ops(ps_malloc_ops_t *ops)
{
    if (ops == NULL) {
        ZF_LOGE("ops is NULL");
        return -1;
    }

    int ret = ps_new_stdlib_malloc_ops(ops);
    if (ret) {
        return ret;
    }

#ifndef NDEBUG
    /* This works as malloc_ops contains pointers */
    malloc_ops_initialised = true;
    io_mapper_malloc_ops = (ps_malloc_ops_t) * ops;
#endif

    return 0;
}

static char *camkes_io_fdt_get(void *cookie)
{
    return (char *)(cookie ? cookie : NULL);
}

int camkes_io_fdt(ps_io_fdt_t *io_fdt)
{
    if (io_fdt == NULL) {
        ZF_LOGE("io_fdt is NULL");
        return -1;
    }

    extern char *dtb_symbol WEAK;

    if (!&dtb_symbol) {
        io_fdt->cookie = NULL;
    } else {
        /* the buffer contains the bootinfo header, so we skip it */
        io_fdt->cookie = (void *) &dtb_symbol + sizeof(seL4_BootInfoHeader);
    }

    io_fdt->get_fn = camkes_io_fdt_get;

    return 0;
}

/* Force the _driver_modules section to be created even if no modules are defined. */
static USED SECTION("_driver_modules") struct {} dummy_driver_module;
/* Definitions so that we can find the list of driver modules that can be initialised */
extern ps_driver_module_t *__start__driver_modules[];
extern ps_driver_module_t *__stop__driver_modules[];

static ll_t *driver_defer_list = NULL;

static int defer_driver_init(ps_io_ops_t *ops, char *device_path, ps_driver_init_fn_t init_func)
{
    if (ops == NULL) {
        ZF_LOGE("ops is NULL");
        return -1;
    }

    if (device_path == NULL) {
        ZF_LOGE("device path is NULL");
        return -1;
    }

    if (init_func == NULL) {
        ZF_LOGE("init_func is NULL");
        return -1;
    }

    camkes_defer_token_t *defer_token = NULL;
    int error = ps_calloc(&ops->malloc_ops, 1, sizeof(*defer_token), (void **) &defer_token);
    if (error) {
        ZF_LOGE("Failed to allocate memory for a bookkeeping structure for the driver defer list");
        return -1;
    }

    defer_token->device_path = device_path;
    defer_token->init_func = init_func;

    error = ll_append(&ops->malloc_ops, &driver_defer_list, defer_token);
    if (error) {
        ZF_LOGE("Failed to add the driver init function to the defer list");
    }

    return 0;
}

static int find_compatible_driver_module(ps_io_ops_t *ops, int node_offset, char *device_path)
{
    if (ops == NULL) {
        ZF_LOGF("ops is NULL");
    }

    char *dtb_blob = ps_io_fdt_get(&ops->io_fdt);
    if (!dtb_blob) {
        ZF_LOGF("No DTB supplied!");
    }

    /* Look through the list of hardware modules that are registered and
     * pick the most suitable one by comparing the module's compatible
     * strings against the device node's */
    for (ps_driver_module_t **module = __start__driver_modules; module < __stop__driver_modules; module++) {
        for (const char **curr_str = (*module)->compatible_list; *curr_str != NULL; curr_str++) {
            int match_ret = fdt_node_check_compatible(dtb_blob, node_offset, *curr_str);
            if (match_ret == 0) {
                /* Found a match! */
                int ret = (*module)->init(ops, device_path);
                if (ret == PS_DRIVER_INIT_DEFER) {
                    ZF_LOGF_IF(defer_driver_init(ops, device_path, (*module)->init),
                               "Failed to defer the initialisation of node %s", device_path);
                    return 0;
                } else if (ret < 0) {
                    ZF_LOGE("Node pointed to by path %s failed to have a driver initialise properly, ignoring", device_path);
                    return -1;
                } else if (ret == PS_DRIVER_INIT_SUCCESS) {
                    return 0;
                } else {
                    ZF_LOGE("Initialisation function for node pointed to by path %s returned an unexpected code", device_path);
                    return -1;
                }
            } else if (match_ret < 0) {
                ZF_LOGE("Node pointed to by path %s is malformed, ignoring", device_path);
                return -1;
            }
            /* Ignore the no match case */
        }
    }

    /* No suitable module was found for this device node */
    ZF_LOGE("No suitable driver was found for path %s, ignoring", device_path);
    return 0;
}

static int handle_defered_modules(ps_io_ops_t *ops)
{
    if (ops == NULL) {
        ZF_LOGF("ops is NULL");
    }

    /* The set of modules that have deferred and that we need to work through */
    ll_t *working_set = driver_defer_list;
    /* The set of modules that have deferred again */
    ll_t *deferred_set = NULL;
    ll_t *deferred_tail = NULL;

    while (working_set != NULL) {
        ll_t *curr = working_set;
        while (curr != NULL) {
            camkes_defer_token_t *defer_token = curr->data;
            int ret = defer_token->init_func(ops, defer_token->device_path);
            if (ret == PS_DRIVER_INIT_DEFER) {
                /* Throw this into deferred set and also remove it from the
                 * working set */
                if (deferred_tail != NULL) {
                    deferred_tail->next = curr;
                }
                if (deferred_set == NULL) {
                    deferred_set = curr;
                }
                deferred_tail = curr;
                curr = curr->next;
                deferred_tail->next = NULL;
            } else {
                /* Diagnostics */
                if (ret < 0) {
                    ZF_LOGE("Node pointed to by path %s failed to have a driver initialise properly, ignoring",
                            defer_token->device_path);
                } else if (ret != PS_DRIVER_INIT_SUCCESS) {
                    ZF_LOGE("Initialisation function for node pointed to by path %s returned an unexpected code",
                            defer_token->device_path);
                }
                /* Remove this from the working set and deallocate memory */
                ll_t *temp = curr;
                curr = curr->next;
                ZF_LOGF_IF(ps_free(&ops->malloc_ops, sizeof(*defer_token), defer_token),
                           "Failed to deallocate a camkes_defer_token_t instance");
                ZF_LOGF_IF(ps_free(&ops->malloc_ops, sizeof(*temp), temp), "Failed to deallocate a ll_t node");
            }
        }
        /* Swap the two sets and continue on */
        working_set = deferred_set;
        deferred_set = NULL;
        deferred_tail = NULL;
    }

    return 0;
}

/* Force the _hardware_init section to be created even if no modules are defined. */
static USED SECTION("_hardware_init") struct {} dummy_init_module;
/* Definitions so that we can find the list of hardware modules that we need to initialise */
extern char **__start__hardware_init[];
extern char **__stop__hardware_init[];

int camkes_call_hardware_init_modules(ps_io_ops_t *ops)
{
    if (__start__hardware_init == __stop__hardware_init) {
        /* Exit early if there are no modules to initialise */
        return 0;
    }

    if (ops == NULL) {
        ZF_LOGE("ops is NULL");
        return -1;
    }

    char *dtb_blob = ps_io_fdt_get(&ops->io_fdt);
    if (!dtb_blob) {
        ZF_LOGE("No DTB supplied!");
        return -1;
    }

    for (char ***curr_path = __start__hardware_init; curr_path < __stop__hardware_init; curr_path++) {
        int node_offset = fdt_path_offset(dtb_blob, **curr_path);
        if (node_offset < 0) {
            ZF_LOGE("Path %s doesn't seem to be in the DTB, ignoring", **curr_path);
            continue;
        }

        /* Quick sanity check to see if the node has a compatible property */
        const void *dummy = fdt_getprop(dtb_blob, node_offset, "compatible", NULL);
        if (dummy == NULL) {
            ZF_LOGE("Node pointed to by path %s doesn't have a compatible string or is malformed, ignoring", **curr_path);
            continue;
        }

        /* Currently most of the errors in this function as they aren't fatal */
        find_compatible_driver_module(ops, node_offset, **curr_path);
    }

    /* Now take care of the deferred modules, again ignore most of the errors
     * in this function as they aren't fatal */
    handle_defered_modules(ops);

    return 0;
}

int camkes_io_ops(ps_io_ops_t *ops)
{
    if (ops == NULL) {
        ZF_LOGE("ops is NULL");
        return -1;
    }

    int ret = camkes_ps_malloc_ops(&ops->malloc_ops);
    if (ret) {
        return ret;
    }

    ret = camkes_io_mapper(&ops->io_mapper) ||
          camkes_io_port_ops(&ops->io_port_ops) ||
          camkes_dma_manager(&ops->dma_manager) ||
          camkes_io_fdt(&ops->io_fdt) ||
          camkes_irq_ops(&ops->irq_ops) ||
          camkes_interface_registration_ops(&ops->interface_registration_ops, &ops->malloc_ops);

    return ret;
}
