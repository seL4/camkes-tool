#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re

Event="Event"
Procedure="Procedure"
Dataport="Dataport"

# List of functions used amongst all classes

def extract_numbers(list_of_tuples_string_numbers):
    """
    Takes a string of numbers, comma separated, and returns a tuple of two numbers at a time.
    Eg: "0,0,96e2,221.5" -> [(0,0),(96e2, 221.5)]
    :param list_of_tuples_string_numbers: Comma separated numbers in string type
    :return: List of tuples, each tuple a set of 2 numbers.
    """

    result = re.findall("([-+]?\d+[.]?\d*[eE]*[-+]*\d*)[,]([-+]?\d+[.]?\d*[eE]*[-+]*\d*)",
                            list_of_tuples_string_numbers)

    new_list = list()
    for next_tuple in result:
        converted_tuple = (float(next_tuple[0]), float(next_tuple[1]))
        new_list.append(converted_tuple)

    return new_list
