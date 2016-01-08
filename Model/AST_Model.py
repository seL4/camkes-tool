#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import sys
import argparse

# TODO: Make CAmkES module importable
from camkes.parser.parser import Parser
from camkes.ast.liftedast import LiftedAST
import camkes.ast


class ASTModel:

    def __init__(self):
        pass

    '''
    A static method that returns an LiftedAST object given a path to the camkes file
    '''
    @staticmethod
    def get_ast(path_to_camkes_file):
        args = argparse.ArgumentParser()
        args.add_argument('--import-path', '-I', help='Add this path to the list of paths to '
                                                           'search for built-in imports. That is, add it to the list '
                                                           'of directories that are searched to find the file "foo" '
                                                           'when encountering an expression "import <foo>;".',
                               action='append', default=[])
        args = args.parse_args(["--import-path",
                                "/home/sthasarathan/Documents/camkes-newExample/tools/camkes/include/builtin"])

        camkes_parser = Parser(args)
        ast, _read = camkes_parser.parse_file(path_to_camkes_file)


        return ast

    @staticmethod
    def find_instance(instance_list, instance_name):

        for instance_object in instance_list:
            assert isinstance(instance_object, camkes.ast.Instance)
            if instance_name == instance_object.name:
                return instance_object

        return None
