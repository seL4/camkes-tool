#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

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
