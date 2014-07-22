#!/bin/bash
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# This generates PLY rules for a CAmkES entity that defines a type. The rules
# generated are:
#  $1_sing   Singleton; only useful for top-level singly-instantiated types
#  $1_decl   A (potentially top-level) declaration
#  $1_ref    A reference to a previously defined type; used when instantiating
#  $1_block  A brace-delimited definition of a type
#  $1_defn   A definition of a type
# See the top-level README for more information about these common rules. Note
# that for generating IDL types you will want to change UnresolvedADLSymbol to
# UnresolvedIDLSymbol in the output.

if [ $# -ne 1 ]; then
    echo "Usage: $0 type" >&2
    exit 1
fi

TYPE=$1
TYPE_LOWER=`echo ${TYPE} | tr '[:upper:]' '[:lower:]'`
INDENT=`echo ${TYPE} | sed 's/./ /g'`

cat <<EOT
# ${TYPE}
def p_${TYPE_LOWER}_sing(t):
    '''${TYPE_LOWER}_sing : ${TYPE_LOWER} ID SEMI
       ${INDENT}      | ${TYPE_LOWER}_decl'''
    if len(t) == 4:
        t[0] = UnresolvedADLSymbol(t[2], ${TYPE})
    else:
        assert len(t) == 2
        t[0] = t[1]
        assert isinstance(t[0], ${TYPE})
def p_${TYPE_LOWER}_decl(t):
    '''${TYPE_LOWER}_decl : ${TYPE_LOWER} ID ${TYPE_LOWER}_block
       ${INDENT}      | ${TYPE_LOWER} ${TYPE_LOWER}_block'''
    if len(t) == 4:
        t[0] = t[3]
        assert isinstance(t[0], ${TYPE})
        t[0].name = t[2]
    else:
        assert len(t) == 3
        t[0] = t[2]
        assert isinstance(t[0], ${TYPE})
def p_${TYPE_LOWER}_ref(t):
    '''${TYPE_LOWER}_ref : ID
       ${INDENT}     | ${TYPE_LOWER}_block'''
    if isinstance(t[1], ${TYPE}):
        t[0] = t[1]
    else:
        t[0] = UnresolvedADLSymbol(t[1], ${TYPE})
def p_${TYPE_LOWER}_block(t):
    '''${TYPE_LOWER}_block : LBRACE ${TYPE_LOWER}_defn RBRACE'''
    t[0] = t[2]
    assert isinstance(t[0], ${TYPE})
def p_${TYPE_LOWER}_defn(t):
    '''${TYPE_LOWER}_defn : FILL ME IN'''
    FILL ME IN
    assert isinstance(t[0], ${TYPE})
EOT
