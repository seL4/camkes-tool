#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

# The Model python module

# This module deals with model side of the program. It communicates with the parser to collect an AST tree (AST_Model.py
# In the future ASTModel will create a unfrozen ast, allowing for editing.

# Common contains all the simple helper functions used throughout the visualCAmkES module.

# A lot of the model work is actually done in other camkes modules (such as parser, ast, runner, etc.)
