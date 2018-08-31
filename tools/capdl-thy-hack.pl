#!/usr/bin/env perl
#
# Copyright 2018, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

# CapDL file filter that removes X (Grant) rights from connector endpoints.
# This hack can be removed when we have a kernel that allows Call
# without Grant; see issue SELFOUR-6.

while (<>) {
    if (/^(.*_ep )\((R)?(W)?X(.*)\)(.*)$/
        # ignore non-connector EPs
        && not /pre_init_ep|post_init_ep|fault_ep/) {
        print "$1($2$3$4)$5\n";
    } else {
        print;
    }
}
