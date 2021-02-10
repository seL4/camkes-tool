<!--
     Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

This is a test suite for running the generated capDL refinement proofs.
These are Isabelle proof scripts, to prove that the generated capDL
respects the isolation properties expected from its CAmkES system
specification.

Currently, the verification only supports apps that use the basic
CAmkES features and connectors.
We plan to extend verification support to more complex CAmkES
assemblies in the future (eventually including a CAmkES VMM).
Also note that only the AARCH32 platform is supported.

When building a CAmkES app, enable proof generation with the
`CAmkESCapDLVerification` option. The proof scripts will be
generated in `projects/camkes` in your build directory. This also
requires `CAmkESCapDLStaticAlloc` to be enabled.

# Tests
The top-level test script is `./run_tests`.

The tests expect to run as part of a
[camkes-manifest](https://github.com/seL4/camkes-manifest) checkout.
In the camkes-manifest repo, do

```
repo sync -m l4v-master.xml
```

This will clone the Isabelle theorem prover and the L4.verified
infrastructure into `projects/l4v`.

Then run the `run_tests` script that is in this directory.
