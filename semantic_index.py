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

import codecs
from lxml import etree
import simplejson
import yaml

from category import Category
from logic_parser import lexpr
from semantic_rule import SemanticRule

class SemanticIndex(object):
    def __init__(self, contents):
        # Input might be a string containing a filename, or a list of rules.
        if isinstance(contents, str) and contents != '':
            self.rules = load_semantic_rules(contents)
        elif isinstance(contents, list):
            self.rules = contents
        else:
            self.rules = []

    def get_relevant_rules(self, rule_pattern):
        """
        Given a rule pattern (that is, a SemanticRule with several features
        specified, but no semantics associated), it searches for relevant
        rules with the same features but with associated semantics.
        """
        relevant_rules = []
        for rule in self.rules:
            if rule.match(rule_pattern):
                relevant_rules.append(rule)
        return relevant_rules

    def get_semantic_representation(self, ccg_tree, tokens):
        rule_pattern = make_rule_pattern_from_ccg_node(ccg_tree, tokens)
        # Obtain the semantic template.
        relevant_rules = self.get_relevant_rules(rule_pattern)
        if not relevant_rules and len(ccg_tree) == 2:
            return None
        elif not relevant_rules:
            semantic_template = build_default_template(rule_pattern, ccg_tree)
            semantic_rule = None
        else:
            semantic_rule = relevant_rules.pop()
            semantic_template = semantic_rule.semantics
        # Apply template to relevant (current, child or children) CCG node(s).
        if len(ccg_tree) == 0:
            base = rule_pattern.attributes.get('base')
            surf = rule_pattern.attributes.get('surf')
            assert base and surf, 'The current CCG node should contain attributes ' \
              + '"base" and "surf". CCG node: {0}\nrule_pattern attributes: {1}'\
              .format(etree.tostring(ccg_tree, pretty_print=True),
                      rule_pattern.attributes)
            predicate_string = base if base != '*' else surf
            predicate = lexpr(predicate_string)
            semantics = semantic_template(predicate).simplify()
            # Assign coq types.
            if semantic_rule != None and 'coq_type' in semantic_rule.attributes:
                coq_types = semantic_rule.attributes['coq_type']
                ccg_tree.set('coq_type',
                  simplejson.dumps(['Parameter {0} : {1}.'.format(predicate_string, coq_types)]))
            else:
                ccg_tree.set('coq_type', "[]")
        elif len(ccg_tree) == 1:
            predicate = lexpr(ccg_tree[0].get('sem'))
            semantics = semantic_template(predicate).simplify()
            # Assign coq types.
            ccg_tree.set('coq_type', ccg_tree[0].attrib.get('coq_type', "[]"))
        else:
            predicate_left  = lexpr(ccg_tree[0].get('sem'))
            predicate_right = lexpr(ccg_tree[1].get('sem'))
            semantics = semantic_template(predicate_left).simplify()
            semantics = semantics(predicate_right).simplify()
            # Assign coq types.
            coq_types_left  = simplejson.loads(ccg_tree[0].attrib.get('coq_type', "[]"))
            coq_types_right = simplejson.loads(ccg_tree[1].attrib.get('coq_type', "[]"))
            coq_types = sorted(coq_types_left + coq_types_right)
            ccg_tree.set('coq_type', simplejson.dumps(coq_types))
        return semantics

def get_attributes_from_ccg_node_recursively(ccg_tree, tokens):
    if 'child' in ccg_tree.attrib:
        attributes = ccg_tree.attrib
        for i, child in enumerate(ccg_tree):
            child_attributes = get_attributes_from_ccg_node_recursively(child, tokens)
            for name, value in child_attributes.items():
                attributes['child' + str(i) + '_' + name] = value
    else:
        attributes = ccg_tree.attrib
        token_id = ccg_tree.get('terminal')
        token_node = find_node_by_id(token_id, tokens)
        attributes.update(token_node.attrib)
    return attributes

def make_rule_pattern_from_ccg_node(ccg_tree, tokens):
    attributes = get_attributes_from_ccg_node_recursively(ccg_tree, tokens)
    category = ccg_tree.get('category')
    assert category, 'There should be a non-empty category attribute in {0}'\
      .format(etree.tostring(ccg_tree, pretty_print=True))
    semantics = None
    rule_pattern = SemanticRule(category, semantics, attributes)
    return rule_pattern

def find_node_by_id(node_id, xml_tree):
    for span in xml_tree:
        if span.get('id') == node_id:
            return span
    raise(ValueError('It should have found a span for id {0}'.format(node_id)))

def load_semantic_rules(fn):
    semantic_rules = []
    loaded = None
    with codecs.open(fn, 'r', 'utf-8') as infile:
        loaded = yaml.load(infile)
    if not loaded: raise ValueError("couldn't load file: " + fn)

    for attributes in loaded:
        # Compulsory fields.
        category = attributes['category']
        semantics = lexpr(attributes['semantics'])
        del attributes['category'], attributes['semantics']
        new_semantic_rule = \
          SemanticRule(category, semantics, attributes)
        semantic_rules.append(new_semantic_rule)
    return semantic_rules

def build_default_template(rule_pattern, ccg_tree):
    category = rule_pattern.category
    if len(ccg_tree) == 0:
        num_arguments = category.get_num_args()
    elif len(ccg_tree) == 1:
        category2 = Category(ccg_tree.get('category'))
        num_arguments = category.get_num_args() - category2.get_num_args()
    variable_names = ['x' + str(i) for i in range(num_arguments)]
    if not variable_names:
        template_string = r'\P.P'
    else:
        template_string =  r'\P ' + ' '.join(variable_names) \
                          + '.P(' + ', '.join(reversed(variable_names)) + ')'
    template = lexpr(template_string)
    return template
