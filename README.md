<!--
 Copyright 2016, NICTA

 This software may be distributed and modified according to the terms of
 the BSD 2-Clause license. Note that NO WARRANTY is provided.
 See "LICENSE_BSD2.txt" for details.

 @TAG(NICTA_BSD)
-->

# CAmkES

This repository contains the code generator and templating system that form the
core of the [CAmkES component platform](https://wiki.sel4.systems/CAmkES/). This
branch, "next," has a from-scratch re-implementation of the architecture
description parser and addresses several shortcomings of the "master" branch.
This branch is intended to supersede "master" in the future.

For more information about CAmkES functionality, see the
[documentation](docs/index.md).

For more information on CAmkES "next", see its [wiki page](https://wiki.sel4.systems/CAmkESNext).

## Dependencies

To install the tools and libraries required to build seL4 and CAmkES next on a
fresh installation of Ubuntu 16.04, run:

```
apt-get install git repo libncurses-dev python-pip libxml2-utils cmake ninja-build clang libssl-dev libsqlite3-dev libcunit1-dev \
gcc-multilib expect qemu-system-x86 qemu-system-arm gcc-arm-none-eabi binutils-arm-none-eabi

pip install six tempita plyplus pyelftools orderedset jinja2

curl -sSL https://get.haskellstack.org/ | sh
```
