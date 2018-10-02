<!--
     Copyright 2018, Data61
     Commonwealth Scientific and Industrial Research Organisation (CSIRO)
     ABN 41 687 119 230.

     This software may be distributed and modified according to the terms of
     the BSD 2-Clause license. Note that NO WARRANTY is provided.
     See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
-->

This is a little framework for generating Isabelle specs about the
CAmkES ADL and capDL, and performing proofs over them.

Eventually, most of this ought to be automated in the main CAmkES tool
and the L4.verified theories. For now, we have manually-written
capDL refinement proofs, which are tested against the ADL and capDL
specs generated from the CAmkES tool.

# Tests
The top-level test script is ./run_tests.

The tests expect to run as part of a camkes-manifest checkout.
You need a branch of the camkes-manifest that has suitable tool
versions and a copy of `l4v`.

In the camkes-manifest repo, do

```
(cd .repo/manifests && git fetch origin &&
    git checkout camkes-cdl-refine-VER-984)
repo sync -m l4v-default.xml
```

Then run the `run_tests` script that is in this directory.
