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

#include <camkes/buffqueue.h>
#include <camkes/buffqueue_template.h>

int camkes_register_buffqueue_channel(int buffqueue_id, size_t size, volatile void *buf, notify_fn_t notify, buffqueue_role_t role) {
    /* Check that the buffqueue_id is in range */
    if(buffqueue_id > MAX_CAMKES_BUFFQUEUE_ID) {
        return -1;
    }
    /* Check that the buffer and notify function are not NULL */
    if(buf == NULL || notify == NULL) {
        return -1;
    }
    /* Initialise the contents of the buffqueue channel */
    buffqueue_channel_t *bq_channel = &buffqueue_channels[buffqueue_id];
    bq_channel->channel_buffer = buf;
    bq_channel->channel_buffer_size = size;
    bq_channel->notify = notify;
    bq_channel->role = role;
    bq_channel->buffer_allocated = 0;
    num_registered_buffqueue_channels++;
    return 0;
}
