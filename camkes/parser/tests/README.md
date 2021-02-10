<!--
     Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# CAmkES Parser Unit Testing

This directory contains a test suite for the CAmkES parser. To run all the
tests:

```bash
runall.py
```

To run a specific set of tests, e.g.:

```bash
teststage3.py
```

Of particular note are the subdirectories of this directory that contain sample
input for the parser. The directory "good" contains various input that
represents valid CAmkES specifications. The directories "bad-at-*" contain
input that represent invalid specifications that should trigger an exception at
the parsing stage indicated by the suffix. Files in these directories are
discovered automatically and tested by the file testexamples.py.
