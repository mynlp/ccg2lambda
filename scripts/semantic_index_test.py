#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2016 Pascual Martinez-Gomez
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

from lxml import etree
import nltk
from nltk.sem.logic import LogicalExpressionException

from ccg2lambda_tools import assign_semantics_to_ccg
from logic_parser import lexpr
from semantic_index import SemanticIndex
from semantic_index import SemanticRule

# TODO: ensure that 'var_paths' is not matching attributes in CCG XML trees.
class GetSemanticRepresentationTestCase(unittest.TestCase):
    def setUp(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
          <token base="base3" pos="pos3" surf="surf3" id="t1_3"/>
          <token base="base4" pos="pos4" surf="surf4" id="t1_4"/>
        </tokens>
        <ccg root="sp1-7">
          <span terminal="t1_1" category="N" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="N" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" category="NP" rule=">" end="3" begin="1" id="sp1-3"/>
          <span terminal="t1_3" category="N" end="4" begin="3" id="sp1-4"/>
          <span terminal="t1_4" category="N" end="5" begin="4" id="sp1-5"/>
          <span child="sp1-4 sp1-5" category="NP" rule=">" end="5" begin="3" id="sp1-6"/>
          <span child="sp1-3 sp1-6" category="NPNP" rule=">" end="5" begin="1" id="sp1-7"/>
        </ccg>
      </sentence>
    """
        self.sentence = etree.fromstring(sentence_str)

    def test_CFG(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'}),
                          SemanticRule(r'NPNP', r'\F1 F2.(F1 -> F2)', {'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(self.sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'(_base1 & _base2) -> (_base3 & _base4)')
        self.assertEqual(expected_semantics, semantics)

    def test_RTG2Paths(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'}),
                          SemanticRule(r'NPNP', r'\F1 F2.(F1 -> F2)',
                                       {'var_paths' : [[0,0], [1,1]], 'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(self.sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'_base1 -> _base4')
        self.assertEqual(expected_semantics, semantics)

    def test_RTG1Path(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'}),
                          SemanticRule(r'NPNP', r'\F1 F2.(F1 -> F2)',
                                       {'var_paths' : [[0,1]], 'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(self.sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'\F2.(_base2 -> F2)')
        self.assertEqual(expected_semantics, semantics)

    def test_RTG3Paths2Vars(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'}),
                          SemanticRule(r'NPNP', r'\F1 F2.(F1 -> F2)',
                                       {'var_paths' : [[0,0], [0,1], [1,0]], 'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(self.sentence, semantic_index)
        with self.assertRaises(nltk.sem.logic.LogicalExpressionException):
            semantics = lexpr(ccg_tree.get('sem', None))

    def test_RTG3Paths3Vars(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'}),
                          SemanticRule(r'NPNP', r'\F1 F2 F3.((F3 & F2) -> F1)',
                                       {'var_paths' : [[0,0], [0,1], [1,0]], 'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(self.sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'((_base3 & _base2) -> _base1)')
        self.assertEqual(expected_semantics, semantics)

    def test_right_arg_bar(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="N" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="N" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" category="NP/NP" rule=">" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)

        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP\NP', r'\F1 F2.(F1 | F2)', {'rule' : '>'}),
                          SemanticRule(r'NP/NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'(_base1 & _base2)')
        self.assertEqual(expected_semantics, semantics)

    def test_left_arg_bar(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="N" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="N" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" category="NP\NP" rule=">" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        parser = etree.XMLParser(encoding='utf-8', remove_blank_text=True)
        sentence = etree.fromstring(sentence_str)

        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP\NP', r'\F1 F2.(F1 | F2)', {'rule' : '>'}),
                          SemanticRule(r'NP/NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'(_base1 | _base2)')
        self.assertEqual(expected_semantics, semantics)

    def test_vertical_bar(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="N" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="N" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" category="NP\NP" rule=">" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)

        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P', {}),
                          SemanticRule(r'NP|NP', r'\F1 F2.(F1 -> F2)', {'rule' : '>'}),
                          SemanticRule(r'NP/NP', r'\F1 F2.(F1 & F2)', {'rule' : '>'})]
        semantic_index.rules = semantic_rules
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = lexpr(ccg_tree.get('sem', None))
        expected_semantics = lexpr(r'(_base1 -> _base2)')
        self.assertEqual(expected_semantics, semantics)

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(GetSemanticRepresentationTestCase)
    suites  = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)
