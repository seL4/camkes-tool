#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#
#
import argparse
import yaml

import os
import six
import logging
from camkes.parser import Query

from .exception import ParseError


class GPIOMatchQuery(Query):
    """ Takes the list of GPIO pins in YAML format and converts it into a Python dictionary. """

    def __init__(self):
        pass

    def resolve(self, args):
        assert isinstance(args, list)
        assert len(args) == 1
        resolved = {}
        if 'pins' not in args[0]:
            raise ParseError(
                "One of the seL4GPIOServer GPIO list doesn't follow the correct format.")
        resolved['query'] = [{'desired-pins': args[0]['pins']}]
        resolved['all-pins'] = self.pin_list['gpio_list']
        return resolved

    @staticmethod
    def get_parser():
        parser = argparse.ArgumentParser('gpio')
        parser.add_argument('--gpio-list',
                            type=str,
                            help='List of GPIO pins in a .yaml format.')
        return parser

    def check_options(self):
        if self.options.gpio_list:
            try:
                with open(self.options.gpio_list, 'rb') as list_file:
                    self.pin_list = yaml.safe_load(list_file)
            except:
                logging.fatal("Failed to parse the GPIO pin list file {0}".format(
                    self.options.gpio_list.name))

    @staticmethod
    def get_query_name():
        return "gpio"

    def get_deps(self):
        return [self.options.gpio_list]
