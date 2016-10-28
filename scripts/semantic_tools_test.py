#!/usr/bin/python3
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

import unittest

from nltk.sem.logic import read_type
from lxml import etree
import simplejson

from nltk.sem.logic import LogicParser

from ccg2lambda_tools import assign_semantics_to_ccg
from knowledge import get_lexical_relations
from logic_parser import lexpr
from nltk2coq import normalize_interpretation
from semantic_index import SemanticRule, SemanticIndex
from semantic_tools import resolve_prefix_to_infix_operations
from semantic_types import (build_dynamic_library, convert_coq_signatures_to_nltk,
    convert_coq_to_nltk_type, merge_dynamic_libraries)

class LexicalRelationsTestCase(unittest.TestCase):
    def test_no_relation(self):
        sentence_1_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="_base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence_2_str = r"""
      <sentence id="s2">
        <tokens>
          <token base="_base3" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_base4" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        ccg_xml_trees = [etree.fromstring(sentence_1_str),
                         etree.fromstring(sentence_2_str)]
        relations = get_lexical_relations(ccg_xml_trees)
        expected_relations = []
        self.assertEqual(expected_relations, relations)

    def test_antonym_relation(self):
        sentence_1_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="large" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="animal" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence_2_str = r"""
      <sentence id="s2">
        <tokens>
          <token base="small" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="animal" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        ccg_xml_trees = [etree.fromstring(sentence_1_str),
                         etree.fromstring(sentence_2_str)]
        relations = get_lexical_relations(ccg_xml_trees)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.']
        self.assertEqual(expected_relations, relations)

    def test_antonym_relationBaseUnderscore(self):
        sentence_1_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="_large" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_animal" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence_2_str = r"""
      <sentence id="s2">
        <tokens>
          <token base="_small" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_animal" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        ccg_xml_trees = [etree.fromstring(sentence_1_str),
                         etree.fromstring(sentence_2_str)]
        relations = get_lexical_relations(ccg_xml_trees)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.']
        self.assertEqual(expected_relations, relations)

    def test_antonym_relations2(self):
        sentence_1_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="_large" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_big" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence_2_str = r"""
      <sentence id="s2">
        <tokens>
          <token base="_small" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="_animal" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        ccg_xml_trees = [etree.fromstring(sentence_1_str),
                         etree.fromstring(sentence_2_str)]
        relations = get_lexical_relations(ccg_xml_trees)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.',
           'Axiom ax_antonym_big_small : forall x, _big x -> _small x -> False.']
        self.assertEqual(expected_relations, relations)

class resolve_prefix_to_infix_operationsTestCase(unittest.TestCase):
    def test_entity_no_concat(self):
        expr_str = str(lexpr(r'ion'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str)
        expected_concat_expr_str = 'ion'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_predicate_concat_no(self):
        expr_str = str(lexpr(r'T(lithium,ion)'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str)
        expected_concat_expr_str = 'T(lithium,ion)'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_predicate_concat_yes(self):
        expr_str = str(lexpr(r'R(lithium,ion)'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str)
        expected_concat_expr_str = 'lithiumion'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_predicate_concat_yesPredF(self):
        expr_str = str(lexpr(r'F(lithium,ion)'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'F')
        expected_concat_expr_str = 'lithiumion'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_predicate_concat_yesPredFSymDash(self):
        expr_str = str(lexpr(r'F(lithium,ion)'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'F', '-')
        expected_concat_expr_str = 'lithium-ion'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_Multipredicate_concat_yesPredFSymDash(self):
        expr_str = str(lexpr(r'F(F(lithium,ion),battery)'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'F', '-')
        expected_concat_expr_str = 'lithium-ion-battery'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_Multipredicate_concat_yesPredFSymDash2(self):
        expr_str = str(lexpr(r'F(lithium,F(ion,battery))'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'F', '-')
        expected_concat_expr_str = 'lithium-ion-battery'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_Multipredicate_concat_yesPredFSymDash3(self):
        expr_str = str(lexpr(r'F(F(lithium,ion),F(ion,battery))'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'F', '-')
        expected_concat_expr_str = 'lithium-ion-ion-battery'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

    def test_Multipredicate_concat_yesPredComplexSymDash(self):
        expr_str = str(lexpr(r'O(C(lithium,ion),CONCAT(ion,battery))'))
        concat_expr_str = resolve_prefix_to_infix_operations(expr_str, 'CONCAT', '-')
        expected_concat_expr_str = 'O(C(lithium,ion),ion-battery)'
        self.assertEqual(expected_concat_expr_str, concat_expr_str)

class build_arbitrary_dynamic_libraryTestCase(unittest.TestCase):
    def test_lexical_unary_one_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {'coq_type' : 'Entity -> Prop'}),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-2">
          <span terminal="t1_1" category="N" end="2" begin="1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" end="2" begin="1" id="sp1-2"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_types = ccg_tree.get('coq_type')
        expected_coq_types = '["Parameter _base1 : Entity -> Prop."]'
        self.assertEqual(expected_coq_types, coq_types)

    def test_lexical_binary_two_types(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P', {'coq_type' : 'Entity -> Prop'}),
                          SemanticRule(r'cat2', r'\P.P', {'coq_type' : 'Entity -> Prop -> Prop'}),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_types = ccg_tree.get('coq_type')
        expected_coq_types = '["Parameter _base1 : Entity -> Prop.",' \
                           + ' "Parameter _base2 : Entity -> Prop -> Prop."]'
        self.assertEqual(expected_coq_types, coq_types)

    def test_lexical_binary_one_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\Q x.Q(x)', {'coq_type' : 'Entity -> Prop'}),
                          SemanticRule(r'NP', r'\P Q x.(P -> Q(x))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_types = ccg_tree.get('coq_type')
        expected_coq_types = '["Parameter _base2 : Entity -> Prop."]'
        self.assertEqual(expected_coq_types, coq_types)

class ArbiAutoTypesTestCase(unittest.TestCase):
    def test_lexical_binary_one_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P x.P(x)'),
                          SemanticRule(r'cat2', r'\P x.P(x)', {'coq_type' : 'Entity -> Prop'}),
                          SemanticRule(r'NP', r'\P Q x.(Q(x) -> P(x))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_lib = simplejson.loads(ccg_tree.get('coq_type'))
        expected_coq_lib = ["Parameter _base2 : Entity -> Prop."]
        self.assertEqual(expected_coq_lib, coq_lib)
        expression = [ccg_tree.get('sem')]
        coq_sig =  convert_coq_signatures_to_nltk(coq_lib)
        nltk_lib = build_dynamic_library(expression, coq_sig)
        lib = merge_dynamic_libraries(coq_lib, nltk_lib, './coqlib.v', sentence)
        expected_lib = ["Parameter _base2 : Entity -> Prop.",
                        "Parameter _base1 : Entity -> Prop."]
        self.assertCountEqual(expected_lib, lib)

    def test_lexical_binary_no_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P x.P(x)'),
                          SemanticRule(r'cat2', r'\P x.P(x)'),
                          SemanticRule(r'NP', r'\P Q x.(Q(x) -> P(x))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_lib = simplejson.loads(ccg_tree.get('coq_type'))
        expected_coq_lib = []
        self.assertEqual(expected_coq_lib, coq_lib)
        expression = [ccg_tree.get('sem')]
        coq_sig =  convert_coq_signatures_to_nltk(coq_lib)
        nltk_lib = build_dynamic_library(expression, coq_sig)
        lib = merge_dynamic_libraries(coq_lib, nltk_lib, './coqlib.v', sentence)
        expected_lib = ["Parameter _base2 : Entity -> Prop.",
                        "Parameter _base1 : Entity -> Prop."]
        self.assertCountEqual(expected_lib, lib)

    def test_lexical_binary_one_nltk_complex_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P x.P(x)'),
                          SemanticRule(r'cat2', r'\Q x y.Q(x, y)'),
                          SemanticRule(r'NP', r'\P Q x y.(P(x) -> Q(x, y))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_lib = simplejson.loads(ccg_tree.get('coq_type'))
        expected_coq_lib = []
        self.assertEqual(expected_coq_lib, coq_lib)
        expression = [ccg_tree.get('sem')]
        coq_sig =  convert_coq_signatures_to_nltk(coq_lib)
        nltk_lib = build_dynamic_library(expression, coq_sig)
        lib = merge_dynamic_libraries(coq_lib, nltk_lib, './coqlib.v', sentence)
        expected_lib = ["Parameter _base2 : Entity -> Entity -> Prop.",
                        "Parameter _base1 : Entity -> Prop."]
        self.assertCountEqual(expected_lib, lib)

    def test_lexical_binary_one_coq_complex_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P x.P(x)'),
                          SemanticRule(r'cat2', r'\Q R S.Q(R, S)', {'coq_type' : 'Prop -> Entity -> Prop'}),
                          SemanticRule(r'NP', r'\P Q x R S.(P(x) -> Q(R, S))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_lib = simplejson.loads(ccg_tree.get('coq_type'))
        expected_coq_lib = ['Parameter _base2 : Prop -> Entity -> Prop.']
        self.assertEqual(expected_coq_lib, coq_lib)
        expression = [ccg_tree.get('sem')]
        coq_sig =  convert_coq_signatures_to_nltk(coq_lib)
        nltk_lib = build_dynamic_library(expression, coq_sig)
        lib = merge_dynamic_libraries(coq_lib, nltk_lib, './coqlib.v', sentence)
        expected_lib = ["Parameter _base2 : Prop -> Entity -> Prop.",
                        "Parameter _base1 : Entity -> Prop."]
        self.assertCountEqual(expected_lib, lib)

    def test_lexical_binary_two_coq_complex_type(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P x R.P(x, R)', {'coq_type' : 'Entity -> Prop -> Prop'}),
                          SemanticRule(r'cat2', r'\Q S T.Q(S, T)', {'coq_type' : 'Prop -> Entity -> Prop'}),
                          SemanticRule(r'NP', r'\P Q x R S T.(Q(x, R) -> P(S, T))', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        coq_lib = simplejson.loads(ccg_tree.get('coq_type'))
        expected_coq_lib = ['Parameter _base1 : Entity -> Prop -> Prop.',
                            'Parameter _base2 : Prop -> Entity -> Prop.']
        self.assertEqual(expected_coq_lib, coq_lib)
        expression = [ccg_tree.get('sem')]
        coq_sig =  convert_coq_signatures_to_nltk(coq_lib)
        nltk_lib = build_dynamic_library(expression, coq_sig)
        lib = merge_dynamic_libraries(coq_lib, nltk_lib, './coqlib.v', sentence)
        expected_lib = ["Parameter _base2 : Prop -> Entity -> Prop.",
                        "Parameter _base1 : Entity -> Prop -> Prop."]
        self.assertCountEqual(expected_lib, lib)

class Coq2NLTKSignaturesTestCase(unittest.TestCase):
    def test_entity(self):
        coq_sig = ['Parameter base1 : Entity.',
                   'Parameter base2 : Prop.']
        nltk_sig = convert_coq_signatures_to_nltk(coq_sig)
        expected_nltk_sig = {'base1' : read_type('e'),
                             'base2' : read_type('t')}
        self.assertEqual(expected_nltk_sig, nltk_sig)

class Coq2NLTKTypesTestCase(unittest.TestCase):
    def test_entity(self):
        coq_type = 'Parameter base : Entity.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('e')}
        self.assertEqual(expected_nltk_type, nltk_type)

    def test_property(self):
        coq_type = 'Parameter base : Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('t')}
        self.assertEqual(expected_nltk_type, nltk_type)

    def test_wrong_type(self):
        coq_type = 'Parameter base : YYY.'
        self.assertRaises(ValueError, convert_coq_to_nltk_type, coq_type)

    def test_entityproperty(self):
        coq_type = 'Parameter base : Entity -> Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('<e,t>')}
        self.assertEqual(expected_nltk_type, nltk_type)

    def test_entityentityproperty(self):
        coq_type = 'Parameter base : Entity -> Entity -> Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('<e,<e,t>>')}
        self.assertEqual(expected_nltk_type, nltk_type)

    def test_entitypropertyproperty(self):
        coq_type = 'Parameter base : Entity -> Prop -> Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('<e,<t,t>>')}
        self.assertEqual(expected_nltk_type, nltk_type)

    @unittest.expectedFailure
    def test_entitypropertyAndproperty(self):
        coq_type = 'Parameter base : (Entity -> Prop) -> Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('<<e,t>,t>>')}
        self.assertEqual(expected_nltk_type, nltk_type)

    @unittest.expectedFailure
    def test_entitypropertyAndpropertyentity(self):
        coq_type = 'Parameter base : (Entity -> Prop) -> Prop.'
        nltk_type = convert_coq_to_nltk_type(coq_type)
        expected_nltk_type = {'base' : read_type('<<e,t>,<t,e>>')}
        self.assertEqual(expected_nltk_type, nltk_type)

class build_dynamic_libraryTestCase(unittest.TestCase):
    def test_entity(self):
        exprs = [lexpr('Python')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter Python : Entity.']
        self.assertEqual(expected_dynamic_library, dynamic_library)

    def test_predicate1_argument1(self):
        exprs = [lexpr('language(Python)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter Python : Entity.',
           'Parameter language : Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_predicate1_argument2(self):
        exprs = [lexpr('language(Python, Scala)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter Python : Entity.',
           'Parameter Scala : Entity.',
           'Parameter language : Entity -> Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_predicate2_argument1_and_2(self):
        exprs = [lexpr('AND(language(Python, Scala), nice(Python))')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter nice : Entity -> Prop.',
           'Parameter Python : Entity.',
           'Parameter Scala : Entity.',
           'Parameter language : Entity -> Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_predicate2_argument1_and_2Exprs2(self):
        exprs = [lexpr('language(Python, Scala)'), lexpr('nice(Python)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter nice : Entity -> Prop.',
           'Parameter Python : Entity.',
           'Parameter Scala : Entity.',
           'Parameter language : Entity -> Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_pred1_prop_prop(self):
        exprs = [lexpr('nice(language(Python, Scala))')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter nice : Prop -> Prop.',
           'Parameter Python : Entity.',
           'Parameter Scala : Entity.',
           'Parameter language : Entity -> Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_pred2_prop_prop(self):
        exprs = [lexpr('nice(language(Python, Scala))'),
                 lexpr('fun(language(Python, Scala))')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter nice : Prop -> Prop.',
           'Parameter fun : Prop -> Prop.',
           'Parameter Python : Entity.',
           'Parameter Scala : Entity.',
           'Parameter language : Entity -> Entity -> Prop.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_exists(self):
        exprs = [lexpr('exists x.P(x)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Prop.',
           'Parameter x : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_exist(self):
        exprs = [lexpr('exist x.P(x)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Prop.',
           'Parameter x : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda1exists1(self):
        exprs = [lexpr('\P.exist x.P(x)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Prop.',
           'Parameter x : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda2exists1(self):
        exprs = [lexpr('\P y.exist x.P(x, y)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Entity -> Prop.',
           'Parameter x : Entity.',
           'Parameter y : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda3exists1(self):
        exprs = [lexpr('\P y.\T.exist x.T(P(x, y))')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Entity -> Prop.',
           'Parameter T : Prop -> Prop.',
           'Parameter x : Entity.',
           'Parameter y : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda3exists2(self):
        exprs = [lexpr('\P y.\T.exist x.exists z.T(P(x, y), z)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Entity -> Prop.',
           'Parameter T : Prop -> Entity -> Prop.',
           'Parameter x : Entity.',
           'Parameter y : Entity.',
           'Parameter z : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda3exists2All1(self):
        exprs = [lexpr('\P y.\T.all w.exist x.exists z.T(P(x, y), z, w)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Entity -> Prop.',
           'Parameter T : Prop -> Entity -> Entity -> Prop.',
           'Parameter w : Entity.',
           'Parameter x : Entity.',
           'Parameter y : Entity.',
           'Parameter z : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

    def test_Lambda3exists2All1Mixed(self):
        exprs = [lexpr('\P y.\T.all w.exists z.T(exist x.P(x, y), z, w)')]
        dynamic_library = build_dynamic_library(exprs)
        expected_dynamic_library = \
          ['Parameter P : Entity -> Entity -> Prop.',
           'Parameter T : Prop -> Entity -> Entity -> Prop.',
           'Parameter w : Entity.',
           'Parameter x : Entity.',
           'Parameter y : Entity.',
           'Parameter z : Entity.']
        for item in dynamic_library:
            self.assertIn(item, expected_dynamic_library)
        self.assertEqual(len(expected_dynamic_library), len(dynamic_library))

class Nltk2coqTestCase(unittest.TestCase):
    def test_predicate1_arg(self):
        nltk_expr = lexpr(r'P(x)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(P x)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_predicate2_args(self):
        nltk_expr = lexpr(r'P(x,y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(P x y)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_predicate3_args(self):
        nltk_expr = lexpr(r'P(x,y,z)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(P x y z)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_predicate3_args1Pred(self):
        nltk_expr = lexpr(r'P(x,y,R(z))')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(P x y (R z))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_negation_predicate(self):
        nltk_expr = lexpr(r'-(P)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(not P)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_Negationpredicate1_arg(self):
        nltk_expr = lexpr(r'-(P(x))')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(not (P x))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_Negationpredicate2_args(self):
        nltk_expr = lexpr(r'-(P(x,y))')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(not (P x y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_conjunction_predicates2(self):
        nltk_expr = lexpr(r'(P & Q)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(and P Q)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_conjunction_predicate2_arg1(self):
        nltk_expr = lexpr(r'(P(x) & Q)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(and (P x) Q)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_conjunction_predicate2_arg1and1(self):
        nltk_expr = lexpr(r'(P(x) & Q(y))')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(and (P x) (Q y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_disjunction_predicates2(self):
        nltk_expr = lexpr(r'(P | Q)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(or P Q)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_disjunction_predicate2_arg1(self):
        nltk_expr = lexpr(r'(P(x) | Q)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(or (P x) Q)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_disjunction_predicate2_arg1and1(self):
        nltk_expr = lexpr(r'(P(x) | Q(y))')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(or (P x) (Q y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_implication_proposition2(self):
        nltk_expr = lexpr(r'P -> Q')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(P -> Q)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_implication_predicate2(self):
        nltk_expr = lexpr(r'P(x) -> Q(y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '((P x) -> (Q y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_lambda1_proposition(self):
        nltk_expr = lexpr(r'\x. A')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(fun x => A)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_lambda1_arg1(self):
        nltk_expr = lexpr(r'\x. P(x)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(fun x => (P x))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_lambda2_args2(self):
        nltk_expr = lexpr(r'\x y. P(x, y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(fun x y => (P x y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_lambda3_args2_pred1(self):
        nltk_expr = lexpr(r'\x y P. P(x, y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(fun x y P => (P x y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_existentialArg1Proposition(self):
        nltk_expr = lexpr(r'exists x. P')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(exists x, P)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_existentialArg1(self):
        nltk_expr = lexpr(r'exists x. P(x)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(exists x, (P x))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_existentialArgs2(self):
        nltk_expr = lexpr(r'exists x y. P(x,y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(exists x y, (P x y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_universal_arg1_proposition(self):
        nltk_expr = lexpr(r'all x. P')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(forall x, P)'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_universal_arg1(self):
        nltk_expr = lexpr(r'all x. P(x)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(forall x, (P x))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_universal_args2(self):
        nltk_expr = lexpr(r'all x y. P(x,y)')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(forall x y, (P x y))'
        self.assertEqual(expected_coq_expr, coq_expr)

    def test_tautology(self):
        nltk_expr = lexpr(r'all x y.TrueP')
        coq_expr = normalize_interpretation(nltk_expr)
        expected_coq_expr = '(forall x y, True)'
        self.assertEqual(expected_coq_expr, coq_expr)

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(build_arbitrary_dynamic_libraryTestCase)
    suite2  = unittest.TestLoader().loadTestsFromTestCase(build_dynamic_libraryTestCase)
    suite3  = unittest.TestLoader().loadTestsFromTestCase(resolve_prefix_to_infix_operationsTestCase)
    suite4  = unittest.TestLoader().loadTestsFromTestCase(Nltk2coqTestCase)
    suite5  = unittest.TestLoader().loadTestsFromTestCase(LexicalRelationsTestCase)
    suite6  = unittest.TestLoader().loadTestsFromTestCase(Coq2NLTKTypesTestCase)
    suite7  = unittest.TestLoader().loadTestsFromTestCase(Coq2NLTKSignaturesTestCase)
    suite8  = unittest.TestLoader().loadTestsFromTestCase(ArbiAutoTypesTestCase)
    suites  = unittest.TestSuite([suite1, suite2, suite3, suite4, suite5, suite6,
                                  suite7, suite8])
    unittest.TextTestRunner(verbosity=2).run(suites)
