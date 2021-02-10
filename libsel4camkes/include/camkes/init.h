/*
 * Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* Component init helpers in CAmkES */

#pragma once

/* functions for synchronizing the interface threads during init, intended to be called
 * from different environments init functions.
 */
int pre_init_interface_sync();
int post_init_interface_sync();

/* entry point for the control threads init routine. This is called after core camkes
 * initialisation and is provided by the chosen component environment.
 */
int component_control_main();

/**
 * Entry point for camkes control threads that sets up the runtime.
 */
void camkes_start_control(int thread_id, void *ipc_buffer_ptr);
