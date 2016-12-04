# -*- coding: utf-8 -*-
#
#  Copyright 2015 Pascual Martinez-Gomez
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.

import copy
import re

from nltk.sem.logic import Expression

from category import Category
from logic_parser import lexpr
from normalization import normalize_token

class SemanticRule(object):
    def __init__(self, category, semantics, attributes = {}):
        if not isinstance(category, Category):
            self.category = Category(category)
        else:
            self.category = category
        if semantics and not isinstance(semantics, Expression):
            self.semantics = lexpr(semantics)
        else:
            self.semantics = semantics
        self.attributes = copy.deepcopy(attributes)
        if 'surf' in self.attributes:
          self.attributes['surf'] = normalize_token(self.attributes['surf'])
        if 'base' in self.attributes:
          self.attributes['base'] = normalize_token(self.attributes['base'])

    def match(self, other):
        # Check class membership and special attribute matches.
        if not isinstance(other, self.__class__) \
           or not isinstance(other.category, self.category.__class__) \
           or not self.category.match(other.category):
            return False
        # If one rule is terminal but not the other, then they do not match.
        if self.is_terminal_rule() != other.is_terminal_rule():
            return False
        # Obtain generic list of attributes from both semantic rules,
        # and check whether they match each other (or are underspecified).
        self_attr_names = set(self.attributes.keys())
        other_attr_names = set(other.attributes.keys())
        attribute_names = self_attr_names.union(other_attr_names)
        attribute_names = self.remove_control_attribute_names(attribute_names)
        for attribute_name in attribute_names:
            self_attr_value = self.attributes.get(attribute_name)
            other_attr_value = other.attributes.get(attribute_name)
            if not attributes_match(attribute_name, self_attr_value, other_attr_value):
                return False
        if not wildcard_match(attribute_names, self.attributes, other.attributes):
            return False
        return True

    def remove_control_attribute_names(self, attribute_names):
        control_attrs = ['var_paths']
        return [a for a in attribute_names if a not in control_attrs]

    def is_terminal_rule(self):
        if 'rule' in self.attributes:
            return False
        for attribute_name in self.attributes:
            if attribute_name.startswith('child'):
                return False
        return True

def attributes_match(attribute_name, src_attr_value, trg_attr_value):
    # If this attribute is an arbitrary type specification, it doesn't count
    # as a rule attribute to match against the CCG tree. Thus, return True.
    if 'coq_type' in attribute_name:
        return True
    # If the attribute is a wildcard, we do not check for match here. return True.
    if '_any_' in attribute_name:
        return True
    if src_attr_value is not None and trg_attr_value is None:
        return False
    if src_attr_value is None and trg_attr_value is not None:
        return True
    if src_attr_value is None and trg_attr_value is None:
        return True
    # Case: src_attr_value is not None and trg_attr_value is not None
    if not 'category' in attribute_name:
        return src_attr_value.lower() == trg_attr_value.lower()
    # Comparing categories needs feature unification:
    src_category = Category(src_attr_value)
    trg_category = Category(trg_attr_value)
    return src_category.match(trg_category)

def any_attribute_matches(attribute_name, src_attributes, trg_attributes):
    wildcard_names = re.findall(r'_any_(.*)', attribute_name)
    assert wildcard_names, 'Attribute name invalid: {0}'.format(attribute_name)
    wildcard_name = wildcard_names[0]
    src_attr_value = src_attributes.get(attribute_name, None)
    assert src_attr_value
    trg_attr_values = [value for key, value in trg_attributes.items() \
                       if key.endswith(wildcard_name)]
    for trg_attr_value in trg_attr_values:
        if wildcard_name == 'category':
            src_category = Category(src_attr_value)
            trg_category = Category(trg_attr_value)
            if src_category.match(trg_category):
                return True
        else:
            if src_attr_value.lower() == trg_attr_value.lower():
                return True
    return False

def wildcard_match(attribute_names, src_attributes, trg_attributes):
    wildcard_attributes = []
    # Obtain attributes specified as a wildcard "any"
    for attribute_name in src_attributes.keys():
        if re.findall(r'_any_', attribute_name):
            wildcard_attributes.append(attribute_name)
    # match of attributes specified by wildcards.
    for attribute_name in wildcard_attributes:
        if not any_attribute_matches(attribute_name, src_attributes, trg_attributes):
            return False
    return True
