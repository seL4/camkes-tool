/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <string.h>
#include <stddef.h>

#include <camkes/interface_registration.h>
#include <utils/util.h>

/* Could have used <utils/list.h> lists but that uses malloc by itself */

/*
 * Two instances of linked lists structs, one nested inside the other.
 * E.g.
 *
 *     --------------------------        --------------------    --------------------
 *     | outer_interface_list_t | -----> | interface_list_t | -> | interface_list_t |
 *     --------------------------        --------------------    --------------------
 *                  |
 *                  V
 *     --------------------------        --------------------
 *     | outer_interface_list_t | -----> | interface_list_t | -> NULL
 *     --------------------------        --------------------
 *                  |
 *                  V
 *                 NULL
 */
typedef struct interface_list interface_list_t;
struct interface_list {
    void *interface_instance;
    char **properties;
    interface_list_t *next;
};

typedef struct outer_interface_list outer_interface_list_t;
struct outer_interface_list {
    ps_interface_type_t interface_type;
    interface_list_t *interface_list;
    outer_interface_list_t *next;
};

typedef struct camkes_interface_cookie {
    ps_malloc_ops_t *malloc_ops;
    outer_interface_list_t *outer_interface_list;
} camkes_interface_cookie_t;

/* Only checks whether or not two interface list nodes are equal. 0 if they are
 * equal (interface_instances match), 1 otherwise. */
static inline int interface_list_comparator(interface_list_t *a, interface_list_t *b)
{
    assert(a && b);
    if (a->interface_instance == b->interface_instance) {
        return 0;
    }
    return 1;
}

SGLIB_DEFINE_LIST_PROTOTYPES(interface_list_t, interface_list_comparator, next);
SGLIB_DEFINE_LIST_FUNCTIONS(interface_list_t, interface_list_comparator, next);

static inline int outer_interface_list_comparator(outer_interface_list_t *a, outer_interface_list_t *b)
{
    assert(a && b);
    if (a->interface_type == b->interface_type) {
        return 0;
    }
    return 1;
}

SGLIB_DEFINE_LIST_PROTOTYPES(outer_interface_list_t, outer_interface_list_comparator, next);
SGLIB_DEFINE_LIST_FUNCTIONS(outer_interface_list_t, outer_interface_list_comparator, next);

/* This is used to destroy any properties array that *we made a copy of* using copy_properties_array() */
static inline void destroy_properties_array(ps_malloc_ops_t *malloc_ops, char **properties)
{
    assert(malloc_ops);
    for (char *curr = *properties; curr != NULL; curr++) {
        size_t property_len = strlen(curr);
        ZF_LOGF_IF(ps_free(malloc_ops, property_len + 1, curr),
                   "Failed to cleanup properties from the properties array");
    }
}

static inline char **copy_properties_array(ps_malloc_ops_t *malloc_ops, char **properties)
{
    assert(malloc_ops && properties);

    /* Find the amount of strings in the array */
    size_t num_strings = 0;
    for (char *curr = *properties; curr != NULL; curr++, num_strings++);

    char **properties_copy = NULL;
    int error = ps_calloc(malloc_ops, 1, sizeof(char *) * num_strings, (void **) &properties_copy);
    if (error) {
        return NULL;
    }

    /* Now go through the entire array and copy the strings */
    for (int i = 0; i < num_strings; i++) {
        size_t property_len = strlen(properties[i]);
        error = ps_calloc(malloc_ops, 1, sizeof(char) * property_len + 1, (void **) &properties_copy[i]);
        if (error) {
            ZF_LOGE("Failed to allocate property %d of %zu properties", i, num_strings);
            destroy_properties_array(malloc_ops, properties_copy);
            return NULL;
        }
        strncpy(properties_copy[i], properties[i], property_len + 1);
    }

    return properties_copy;
}

int camkes_interface_register(void *cookie, ps_interface_type_t interface_type, void *interface_instance,
                              char **properties)
{
    if (!interface_instance && interface_type != PS_NULL_INTERFACE) {
        ZF_LOGE("Empty interface instance!");
        return -EINVAL;
    }

    int error = 0;
    int ret = 0;

    camkes_interface_cookie_t *interface_cookie = cookie;

    /* Check if there will be duplicate interface instances (same ptr) if we
     * add this new instance in */
    outer_interface_list_t dummy_outer_node = { .interface_type = interface_type };
    outer_interface_list_t *outer_member = sglib_outer_interface_list_t_find_member(interface_cookie->outer_interface_list,
                                                                                    &dummy_outer_node);
    bool allocated_outer_member = false;
    if (outer_member) {
        interface_list_t dummy_inner_node = { .interface_instance = interface_instance };
        interface_list_t *inner_member = sglib_interface_list_t_find_member(outer_member->interface_list,
                                                                            &dummy_inner_node);
        if (!inner_member) {
            /* Found a duplicate */
            ZF_LOGE("Trying to add the same interface instance into same interface type!");
            return -EINVAL;
        }
    } else {
        /* We now need to create a new outer list node for this interface type */
        error = ps_calloc(interface_cookie->malloc_ops, 1, sizeof(*outer_member), (void **) &outer_member);
        if (error) {
            ZF_LOGE("Failed to allocate memory for a new node for the interface type");
            return -ENOMEM;
        }
        /* Don't add it the of the outer interface list yet, as clean-up becomes problematic */
        outer_member->interface_type = interface_type;
        allocated_outer_member = true;
    }

    interface_list_t *new_node = NULL;
    error = ps_calloc(interface_cookie->malloc_ops, 1, sizeof(*new_node), (void **) &new_node);
    if (error) {
        ZF_LOGE("Failed to allocate memory for a new node for the interface instance");
        ret = -ENOMEM;
        goto fail;
    }

    char **properties_copy = NULL;
    if (properties) {
        char **properties_copy = copy_properties_array(interface_cookie->malloc_ops, properties);
        if (!properties_copy) {
            ret = -ENOMEM;
            goto fail;
        }
    }

    new_node->interface_instance = interface_instance;
    new_node->properties = properties_copy;

    sglib_interface_list_t_add(&outer_member->interface_list, new_node);

    if (allocated_outer_member) {
        /* Now we join this outer node into the outer list */
        sglib_outer_interface_list_t_add(&interface_cookie->outer_interface_list, outer_member);
    }

    return 0;

fail:
    if (allocated_outer_member) {
        ZF_LOGF_IF(ps_free(interface_cookie->malloc_ops, sizeof(*outer_member), outer_member),
                   "Failed to cleanup after a failed interface register operation");
    }

    if (new_node) {
        ZF_LOGF_IF(ps_free(interface_cookie->malloc_ops, sizeof(*new_node), new_node),
                   "Failed to cleanup after a failed interface register operation");
    }

    return ret;
}

int camkes_interface_unregister(void *cookie, ps_interface_type_t interface_type, void *interface_instance)
{
    if (!interface_instance && interface_type != PS_NULL_INTERFACE) {
        ZF_LOGE("Empty interface instance!");
        return -EINVAL;
    }

    camkes_interface_cookie_t *interface_cookie = cookie;

    /* Grab the outer node for this interface type */
    outer_interface_list_t dummy_outer_node = { .interface_type = interface_type };
    outer_interface_list_t *outer_member = sglib_outer_interface_list_t_find_member(interface_cookie->outer_interface_list,
                                                                                    &dummy_outer_node);
    if (!outer_member) {
        /* No outer node for this interface type, so that means that no
         * interface was ever registered for this type. Just ignore. */
        return 0;
    }

    interface_list_t dummy_node = { .interface_instance = interface_instance };
    interface_list_t *target_node = NULL;
    int deleted = sglib_interface_list_t_delete_if_member(&outer_member->interface_list, &dummy_node,
                                                          &target_node);
    if (deleted) {
        /* Only free memory if we've actually deleted something from the list,
         * also carry on as if nothing went wrong if we didn't delete aything
         * */
        if (target_node->properties) {
            destroy_properties_array(interface_cookie->malloc_ops, target_node->properties);
        }
        ZF_LOGF_IF(ps_free(interface_cookie->malloc_ops, sizeof(*target_node), target_node),
                   "Failed to free memory after unregistering an interface");
    }

    return 0;
}

int camkes_interface_find(void *cookie, ps_interface_type_t interface_type, ps_interface_search_handler_fn_t handler,
                          void *handler_data)
{
    if (!handler) {
        ZF_LOGE("No handler provided!");
        return -EINVAL;
    }

    camkes_interface_cookie_t *interface_cookie = cookie;

    outer_interface_list_t dummy_node = { .interface_type = interface_type };
    outer_interface_list_t *outer_member = sglib_outer_interface_list_t_find_member(interface_cookie->outer_interface_list,
                                                                                    &dummy_node);
    if (!outer_member) {
        /* A list for this interface type does not exist yet and hence no entry
         * that we can look at */
        return -ENOENT;
    }

    int handler_ret = 0;

    for (interface_list_t *curr = outer_member->interface_list; curr != NULL; curr = curr->next) {
        handler_ret = handler(handler_data, curr->interface_instance, curr->properties);
        if (handler_ret < 0) {
            /* Error in the handler */
            return handler_ret;
        } else if (handler_ret == PS_INTERFACE_FOUND_MATCH) {
            /* Handler found a match */
            return 0;
        }
    }

    /* We've found no match whatsoever, so we return an error */
    return -ENOENT;
}

int camkes_interface_registration_ops(ps_interface_registration_ops_t *interface_ops, ps_malloc_ops_t *malloc_ops)
{
    if (!interface_ops || !malloc_ops) {
        ZF_LOGE("Arguments are NULL!");
        return -EINVAL;
    }

    camkes_interface_cookie_t *cookie = NULL;
    int error = 0;

    error = ps_calloc(malloc_ops, 1, sizeof(camkes_interface_cookie_t), (void **) &cookie);
    if (error) {
        return -ENOMEM;
    }

    cookie->malloc_ops = malloc_ops;

    interface_ops->cookie = cookie;
    interface_ops->interface_register_fn = camkes_interface_register;
    interface_ops->interface_unregister_fn = camkes_interface_unregister;
    interface_ops->interface_find_fn = camkes_interface_find;

    return 0;
}
