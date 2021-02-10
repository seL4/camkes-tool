#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import re

Event="Event"
Procedure="Procedure"
Dataport="Dataport"

# List of functions used amongst all classes

# Find all floats with a string
# Numbers may start with + or -
# Numbers may be decimal point
# Numbers may be exponential
#         exponential may be + or -
string_floats = re.compile(r'[-+]?\d+[.]?\d*[eE]*[-+]*\d*')

def extract_numbers(list_of_tuples_string_numbers):
    """
    Takes a string of numbers, comma separated, and returns a tuple of two numbers at a time.
    Eg: '"0,0,96e2,221.5"' -> [(0,0),(96e2, 221.5)]
    :param list_of_tuples_string_numbers: Comma separated numbers in string type, assumes even amount of numbers.
    :return: List of tuples, each tuple a set of 2 numbers.
    """

    str_nums_list = string_floats.findall(list_of_tuples_string_numbers)

    new_list = list()
    i = 0
    while i < len(str_nums_list):
        converted_tuple = (float(str_nums_list[i]), float(str_nums_list[i+1]))
        new_list.append(converted_tuple)
        i+=2

    return new_list
