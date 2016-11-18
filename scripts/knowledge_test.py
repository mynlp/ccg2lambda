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

from lxml import etree

from knowledge import get_lexical_relations

class LexicalRelationsTestCase(unittest.TestCase):
    def test_no_relation(self):
        doc_str = r"""
    <root><document><sentences>
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
    </sentences></document></root>
    """
        doc = etree.fromstring(doc_str)
        relations = get_lexical_relations(doc)
        expected_relations = []
        self.assertEqual(expected_relations, relations)

    def test_antonym_relation(self):
        doc_str = r"""
    <root><document><sentences>
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
    </sentences></document></root>
    """
        doc = etree.fromstring(doc_str)
        relations = get_lexical_relations(doc)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.']
        self.assertCountEqual(expected_relations, relations)

    def test_antonym_relationBaseUnderscore(self):
        doc_str = r"""
    <root><document><sentences>
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
    </sentences></document></root>
    """
        doc = etree.fromstring(doc_str)
        relations = get_lexical_relations(doc)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.']
        self.assertEqual(expected_relations, relations)

    def test_antonym_relations2(self):
        doc_str = r"""
    <root><document><sentences>
      <sentence id="s1">
        <tokens>
          <token base="large" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="big" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
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
    </sentences></document></root>
    """
        doc = etree.fromstring(doc_str)
        relations = get_lexical_relations(doc)
        expected_relations = \
          ['Axiom ax_antonym_large_small : forall x, _large x -> _small x -> False.',
           'Axiom ax_antonym_big_small : forall x, _big x -> _small x -> False.']
        self.assertCountEqual(expected_relations, relations)

if __name__ == '__main__':
    suite1 = unittest.TestLoader().loadTestsFromTestCase(LexicalRelationsTestCase)
    suites = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)
