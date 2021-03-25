/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <autoconf.h>
#include <sel4camkes/gen_config.h>
#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <string.h>
#include <sys/utsname.h>
#include <utils/util.h>

/* Dummy pointer for use in sizeof calculations below. */
extern struct utsname *dummy;

/* utsname fields that can be set by applications. As an invariant, we maintain these as
 * NUL-terminated strings.
 */
static char nodename[sizeof dummy->nodename];
#ifdef _GNU_SOURCE
static char domainname[sizeof dummy->domainname];
#else
static char domainname[sizeof dummy->__domainname];
#endif

long camkes_sys_uname(va_list ap)
{

    struct utsname *buf = va_arg(ap, struct utsname *);

    /* Check buf is valid. */
    if (buf == NULL) {
        return -EFAULT;
    }

    /* Set the operating system name. */
    static const char *sysname = "CAmkES/seL4";
    strncpy(buf->sysname, sysname, sizeof buf->sysname);
    buf->sysname[sizeof buf->sysname - 1] = '\0';

    /* Set the network name. */
    memcpy(buf->nodename, nodename, sizeof buf->nodename);

    /* No relevant release information to set. */
    buf->release[0] = '\0';

    /* No relevant version information to set. */
    buf->version[0] = '\0';

    /* Set hardware information. */
    char *arch;
    char *arch_ver;
    char *plat;

#if defined(CONFIG_ARCH_ARM)
    arch = "ARM";
    plat = STRINGIFY(CONFIG_ARM_PLAT);
#if defined(CONFIG_ARCH_ARM_V6)
    arch_ver = "v6";
#elif defined(CONFIG_ARCH_ARM_V7A)
    arch_ver = "v7a";
#elif defined(CONFIG_ARCH_ARM_V7VE)
    arch_ver = "v7a-ve";
#elif defined(CONFIG_ARCH_ARM_V8A)
    arch_ver = "v8a, " STRINGIFY(CONFIG_SEL4_ARCH);
#else
#error "please define ARM architecture"
#endif

#elif defined(CONFIG_ARCH_RISCV)
    arch = "RISC-V";
    arch_ver = ", " STRINGIFY(CONFIG_SEL4_ARCH);
    plat = STRINGIFY(CONFIG_RISCV_PLAT);

#elif defined(CONFIG_ARCH_IA32) || defined(CONFIG_ARCH_X86_64)
    arch = STRINGIFY(CONFIG_SEL4_ARCH);
    arch_ver = "";
    plat = "pc99";

#else
#error "please define configuration"
#endif

    snprintf(buf->machine, sizeof buf->machine, "%s (%s%s)", plat, arch, arch_ver);

    /* Set the domain name. */
#if _GNU_SOURCE
    memcpy(buf->domainname, domainname, sizeof buf->domainname);
#else
    memcpy(buf->__domainname, domainname, sizeof buf->__domainname);
#endif

    return 0;
}

long camkes_sys_sethostname(va_list ap)
{

    const char *name = va_arg(ap, const char *);
    size_t len = va_arg(ap, size_t);

    /* Check name. */
    if (name == NULL) {
        return -EFAULT;
    }

    /* Check length. */
    if (len > sizeof nodename - 1) {
        return -EINVAL;
    }

    /* Set the hostname. This will now be the value returned by later calls to gethostname/uname.
     */
    strncpy(nodename, name, sizeof nodename);
    nodename[sizeof nodename - 1] = '\0';

    return 0;
}

long camkes_sys_setdomainname(va_list ap)
{

    const char *name = va_arg(ap, const char *);
    size_t len = va_arg(ap, size_t);

    /* Check name. */
    if (name == NULL) {
        return -EFAULT;
    }

    /* Check length. */
    if (len > sizeof domainname - 1) {
        return -EINVAL;
    }

    /* Set the domain name. This will now be the value returned by later calls to
     * getdomainname/uname.
     */
    strncpy(domainname, name, sizeof domainname);
    domainname[sizeof domainname - 1] = '\0';

    return 0;
}
