/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <autoconf.h>
#include <camkes/version.h>
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

long camkes_sys_uname(va_list ap) {

    struct utsname *buf = va_arg(ap, struct utsname*);

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

    /* Set the CAmkES release. */
    strncpy(buf->release, camkes_release, sizeof buf->release);
    buf->release[sizeof buf->release - 1] = '\0';

    /* No relevant version information to set. */
    buf->version[0] = '\0';

    /* Set hardware information. */
    char *arch;
    if (config_set(CONFIG_ARCH_ARM)) {
        arch = "ARM";
    } else if (config_set(CONFIG_ARCH_X86)) {
        arch = "x86";
    } else {
        arch = "unknown";
    }
    char *armv;
    if (config_set(CONFIG_ARM_V6)) {
        armv = "v6";
    } else if (config_set(CONFIG_ARM_V7A)) {
        armv = "v7a";
    } else if (config_set(CONFIG_ARM_V8A)) {
        armv = "v8a";
    } else {
        armv = "";
    }
    char *plat;
    if (config_set(CONFIG_PLAT_KZM)) {
        plat = "KZM";
    } else if (config_set(CONFIG_PLAT_OMAP3)) {
        plat = "OMAP3";
    } else if (config_set(CONFIG_PLAT_ARM335X)) {
        plat = "ARM335X";
    } else if (config_set(CONFIG_PLAT_EXYNOS4)) {
        plat = "EXYNOS4";
    } else if (config_set(CONFIG_PLAT_EXYNOS5410)) {
        plat = "EXYNOS5410";
    } else if (config_set(CONFIG_PLAT_EXYNOS5422)) {
        plat = "EXYNOS5422";
    } else if (config_set(CONFIG_PLAT_EXYNOS5250)) {
        plat = "EXYNOS5250";
    } else if (config_set(CONFIG_PLAT_APQ8064)) {
        plat = "APQ8064";
    } else if (config_set(CONFIG_PLAT_SABRE)) {
        plat = "IMX6";
    } else if (config_set(CONFIG_PLAT_WANDQ)) {
        plat = "WANDQ";
    } else if (config_set(CONFIG_PLAT_IMX7_SABRE)) {
        plat = "IMX7";
    } else if (config_set(CONFIG_PLAT_ZYNQ7000)) {
        plat = "ZYNQ7000";
    } else if (config_set(CONFIG_PLAT_PC99)) {
        plat = "PC99";
    } else if (config_set(CONFIG_PLAT_ALLWINNERA20)) {
        plat = "ALLWINNERA20";
    } else if (config_set(CONFIG_PLAT_TK1)) {
        plat = "TK1";
    } else if (config_set(CONFIG_PLAT_HIKEY)) {
        plat = "HIKEY";
    } else {
        plat = "unknown";
    }
    snprintf(buf->machine, sizeof buf->machine, "%s%s %s", arch, armv, plat);

    /* Set the domain name. */
#if _GNU_SOURCE
    memcpy(buf->domainname, domainname, sizeof buf->domainname);
#else
    memcpy(buf->__domainname, domainname, sizeof buf->__domainname);
#endif

    return 0;
}

long camkes_sys_sethostname(va_list ap) {

    const char *name = va_arg(ap, const char*);
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

long camkes_sys_setdomainname(va_list ap) {

    const char *name = va_arg(ap, const char*);
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
