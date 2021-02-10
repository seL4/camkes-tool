/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes/io.h>
#include <camkes/arch/io.h>
#include <sel4/sel4.h>
#include <utils/util.h>

/* Force the _ioport_region section to be created even if no modules are defined. */
static USED SECTION("_ioport_regions") struct {} dummy_ioport_region;
/* Definitions so that we can find the exposed IO port regions */
extern ioport_region_t *__start__ioport_regions[];
extern ioport_region_t *__stop__ioport_regions[];

extern const char *get_instance_name(void);

/* Iterates through all the allocated IO port regions and tries to find one that fits */
static ioport_region_t *find_io_port_region(uint16_t port)
{
    for (ioport_region_t **region = __start__ioport_regions;
         region < __stop__ioport_regions; region++) {
        if (port >= (*region)->start && port <= (*region)->end) {
            return *region;
        }
    }
    return NULL;
}

/* Calls the error handler if there was an error with a syscall */
static int syscall_error_handler(int error, int syscall_label, ioport_region_t *region)
{
    ERR_IF(error != 0, region->error_handler, ((camkes_error_t) {
        .type = CE_SYSCALL_FAILED,
        .instance = get_instance_name(),
        .interface = *(region->interface_name),
        .description = "failed to read from IO port",
        .syscall = syscall_label,
        .error = error,
    }), ({
        return -1;
    }));

    return 0;
}

static int camkes_arch_io_port_in8(ioport_region_t *region, uint16_t port, uint32_t *result)
{
    seL4_X86_IOPort_In8_t reply = seL4_X86_IOPort_In8(region->cap, port);

    int ret = syscall_error_handler(reply.error, X86IOPortIn8, region);
    if (ret) {
        return ret;
    }

    *result = reply.result;

    return 0;
}

static int camkes_arch_io_port_in16(ioport_region_t *region, uint16_t port, uint32_t *result)
{
    seL4_X86_IOPort_In16_t reply = seL4_X86_IOPort_In16(region->cap, port);

    int ret = syscall_error_handler(reply.error, X86IOPortIn16, region);
    if (ret) {
        return ret;
    }

    *result = reply.result;

    return 0;
}

static int camkes_arch_io_port_in32(ioport_region_t *region, uint16_t port, uint32_t *result)
{
    seL4_X86_IOPort_In32_t reply = seL4_X86_IOPort_In32(region->cap, port);

    int ret = syscall_error_handler(reply.error, X86IOPortIn32, region);
    if (ret) {
        return ret;
    }

    *result = reply.result;

    return 0;
}

static int camkes_arch_io_port_out8(ioport_region_t *region, uint16_t port, uint32_t value)
{
    uint8_t val = (uint8_t) value;
    int reply = seL4_X86_IOPort_Out8(region->cap, port, val);

    int ret = syscall_error_handler(reply, X86IOPortOut8, region);
    if (ret) {
        return ret;
    }

    return 0;
}

static int camkes_arch_io_port_out16(ioport_region_t *region, uint16_t port, uint32_t value)
{
    uint16_t val = (uint16_t) value;
    int reply = seL4_X86_IOPort_Out16(region->cap, port, val);

    int ret = syscall_error_handler(reply, X86IOPortOut16, region);
    if (ret) {
        return ret;
    }

    return 0;
}

static int camkes_arch_io_port_out32(ioport_region_t *region, uint16_t port, uint32_t value)
{
    int reply = seL4_X86_IOPort_Out32(region->cap, port, value);

    int ret = syscall_error_handler(reply, X86IOPortOut32, region);
    if (ret) {
        return ret;
    }

    return 0;
}

int camkes_arch_io_port_in(uint32_t port, int io_size, uint32_t *result)
{
    ioport_region_t *region = find_io_port_region((uint16_t) port);
    if (!region) {
        return -1;
    }

    switch (io_size) {
    case IOSIZE_8:
        return camkes_arch_io_port_in8(region, port, result);
    case IOSIZE_16:
        return camkes_arch_io_port_in16(region, port, result);
    case IOSIZE_32:
        return camkes_arch_io_port_in32(region, port, result);
    default:
        return -1;
    }
}

int camkes_arch_io_port_out(uint32_t port, int io_size, uint32_t value)
{
    ioport_region_t *region = find_io_port_region((uint16_t) port);
    if (!region) {
        return -1;
    }

    switch (io_size) {
    case IOSIZE_8:
        return camkes_arch_io_port_out8(region, port, value);
    case IOSIZE_16:
        return camkes_arch_io_port_out16(region, port, value);
    case IOSIZE_32:
        return camkes_arch_io_port_out32(region, port, value);
    default:
        return -1;
    }
}
