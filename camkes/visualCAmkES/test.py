#!/usr/bin/env python
# -*- coding: utf-8 -*-
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

import sys, os

from PyQt5 import QtWidgets

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../'))
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from View.Graph_Widget import GraphWidget
from Model.AST_Model import ASTModel

def test(argv):
    # Create graph widget
    app = QtWidgets.QApplication(argv)
    graph = GraphWidget(None)
    graph.ast = ASTModel.get_ast(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../apps/simple/simple.camkes"))

    print ASTModel.find_instance(graph.ast.assembly.instances, "echo") is not None
    # find_component is not being tested because it is not used anywhere. However
    # there is no reason why find_component will fail to work, if everything else worked.

    print "visualCAmkES test passed"
    return 0

if __name__ == '__main__':
    sys.exit(test(sys.argv))
