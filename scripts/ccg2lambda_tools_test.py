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
from nltk.sem.logic import Expression

from ccg2lambda_tools import (assign_semantics_to_ccg, type_raise, build_ccg_tree)
from logic_parser import lexpr
from semantic_index import (SemanticRule, SemanticIndex,
                            get_attributes_from_ccg_node_recursively, find_node_by_id)

class TypeRaiseTestCase(unittest.TestCase):
    def test_const_expr_raised1(self):
        expr = lexpr(r'nice')
        order = 1
        raised_expr = type_raise(expr, order)
        expected_raised_expr = lexpr(r'\X.nice(X)')
        self.assertEqual(expected_raised_expr, raised_expr)

    def test_expr_raised1(self):
        expr = lexpr(r'\x.nice(x)')
        order = 1
        raised_expr = type_raise(expr, order)
        expected_raised_expr = lexpr(r'\P x.nice(P(x))')
        self.assertEqual(expected_raised_expr, raised_expr)

    def test_expr_raised2(self):
        expr = lexpr(r'\x.nice(x)')
        order = 2
        raised_expr = type_raise(expr, order)
        expected_raised_expr = lexpr(r'\P Q x.nice(P(Q, x))')
        self.assertEqual(expected_raised_expr, raised_expr)

class AssignSemanticsToCCGTestCase(unittest.TestCase):
    def setUp(self):
        self.semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'NP', r'\P.P'),
                          SemanticRule(r'NP/NP', r'\P Q x.(Q(x) & P(x))',
                                       {'rule' : 'ADN'}),
                          SemanticRule(r'S\NP', r'\P x.P(x)'),
                          SemanticRule(r'S/S', r'\P x.P(x)'),
                          SemanticRule(r'S\NP\NP', r'\P y x.P(x, y)'),
                          SemanticRule(r'S\NP\NP\NP', r'\P z y x.P(x, y, z)'),
                          SemanticRule(r'default', r'\P x.x')]
        self.semantic_index.rules = semantic_rules

    def test_token_to_const_latin(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="*" pos="名詞-固有名詞-組織" surf="Scala" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP[mod=nm,case=nc]" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_Scala')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_token_to_const_japanese(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="言語" pos="名詞-一般" surf="言語" id="t0_3"/>
        </tokens>
        <ccg root="sp0-9">
          <span terminal="t0_3" category="NP[mod=nm,case=nc]" end="4" begin="3" id="sp0-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_言語')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_token_to_function_1arg(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="です" katsuyou="基本形" pos="助動詞" surf="です" id="t0_4"/>
        </tokens>
        <ccg root="sp0-10">
          <span terminal="t0_4" category="S[mod=nm,form=base]\NP[mod=nm,case=nc]" end="5" begin="4" id="sp0-10"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x._です(x)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    @unittest.expectedFailure
    def test_token_to_function_2args(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="は" pos="助詞-係助詞" surf="は" id="t0_1"/>
        </tokens>
        <ccg root="sp0-4">
          <span terminal="t0_1" category="(S/S)\NP[mod=nm,case=nc]" end="2" begin="1" id="sp0-4"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x y._は(y, x)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_typeraising_for_unary_pred(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="良い" katsuyou="基本形" pos="形容詞-自立" surf="良い" id="t0_2"/>
        </tokens>
        <ccg root="sp0-7">
          <span child="sp0-8" rule="ADN" category="NP[case=nc]/NP[case=nc]" end="3" begin="2" id="sp0-7"/>
          <span terminal="t0_2" category="S[mod=adn,form=base]" end="3" begin="2" id="sp0-8"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\P x.(P(x) & _良い(x))')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_func_application_forward(self):
        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="良い" katsuyou="基本形" pos="形容詞-自立" surf="良い" id="t0_2"/>
          <token base="言語" pos="名詞-一般" surf="言語" id="t0_3"/>
        </tokens>
        <ccg root="sp0-6">
          <span child="sp0-7 sp0-9" rule="&gt;" category="NP[mod=nm,case=nc]" end="4" begin="2" id="sp0-6"/>
          <span child="sp0-8" rule="ADN" category="NP[case=nc]/NP[case=nc]" end="3" begin="2" id="sp0-7"/>
          <span terminal="t0_2" category="S[mod=adn,form=base]" end="3" begin="2" id="sp0-8"/>
          <span terminal="t0_3" category="NP[mod=nm,case=nc]" end="4" begin="3" id="sp0-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x.(_言語(x) & _良い(x))')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_func_application_backward(self):
        # 'は' has category (S/S)\NP[mod=nm,case=nc] which is not in the
        # unittest semantic templates. Thus, it is assigned the default
        # \E O.O and 'Scala' becomes the final meaning representation.

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="*" pos="名詞-固有名詞-組織" surf="Scala" id="t0_0"/>
          <token base="は" pos="助詞-係助詞" surf="は" id="t0_1"/>
        </tokens>
        <ccg root="sp0-2">
          <span child="sp0-3 sp0-4" rule="&lt;" category="S/S" end="2" begin="0" id="sp0-2"/>
          <span terminal="t0_0" category="NP[mod=nm,case=nc]" end="1" begin="0" id="sp0-3"/>
          <span terminal="t0_1" category="(S/S)\NP[mod=nm,case=nc]" end="2" begin="1" id="sp0-4"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_Scala')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_func_combination_backward(self):
        # Note: the rule that signals function combination contains the "B" character.
        # "です" disappears.
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="簡潔" pos="名詞-形容動詞語幹" surf="簡潔" id="t1_3"/>
          <token base="です" katsuyou="基本形" pos="助動詞" surf="です" id="t1_4"/>
        </tokens>
        <ccg root="sp1-7">
          <span child="sp1-8 sp1-9" rule="&lt;B" category="S[mod=nm,form=base]\NP[mod=nm,case=ga]" end="5" begin="3" id="sp1-7"/>
          <span terminal="t1_3" category="S[mod=nm,form=da]\NP[mod=nm,case=ga]" end="4" begin="3" id="sp1-8"/>
          <span terminal="t1_4" category="S[mod=nm,form=base]\S[mod=nm,form=da]" end="5" begin="4" id="sp1-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x._簡潔(x)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_func_combination_backwardSimple(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="F" pos="pos1" surf="F" id="t1_3"/>
          <token base="G" katsuyou="katsuyou2" pos="pos2" surf="G" id="t1_4"/>
        </tokens>
        <ccg root="sp1-7">
          <span child="sp1-8 sp1-9" rule="&lt;B" category="S[mod=nm,form=base]\NP[mod=nm,case=ga]" end="5" begin="3" id="sp1-7"/>
          <span terminal="t1_3" category="S[mod=nm,form=da]\NP[mod=nm,case=ga]" end="4" begin="3" id="sp1-8"/>
          <span terminal="t1_4" category="S[mod=nm,form=base]\S[mod=nm,form=da]" end="5" begin="4" id="sp1-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x._F(x)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    @unittest.expectedFailure
    def test_func_combination_backwardSimpleTwoArgs(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="F" pos="pos1" surf="F" id="t1_3"/>
          <token base="G" katsuyou="katsuyou2" pos="pos2" surf="G" id="t1_4"/>
        </tokens>
        <ccg root="sp1-7">
          <span child="sp1-8 sp1-9" rule="&lt;B2" category="S[mod=nm,form=base]\NP[mod=nm,case=ga]\NP" end="5" begin="3" id="sp1-7"/>
          <span terminal="t1_3" category="S[mod=nm,form=da]\NP[mod=nm,case=ga]\NP" end="4" begin="3" id="sp1-8"/>
          <span terminal="t1_4" category="S[mod=nm,form=base]\S[mod=nm,form=da]" end="5" begin="4" id="sp1-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\y x._G(_F(x, y))')
        self.assertEqual(expected_semantics, lexpr(semantics))

    @unittest.expectedFailure
    def test_func_combination_backwardComplexTwoArgs(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'S\NP\NP', r'\P y x e. P(e, x, y)'),
                          SemanticRule(r'S\S', r'\P Q e. AND(past(e), Q(e))')]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token id="s1_4" surf="ほめ" pos="動詞" pos1="自立" pos2="*" pos3="*" inflectionType="一段" inflectionForm="連用形" base="ほめる" reading="ホメ"/>
          <token id="s1_5" surf="た" pos="助動詞" pos1="*" pos2="*" pos3="*" inflectionType="特殊・タ" inflectionForm="基本形" base="た" reading="タ"/>
        </tokens>
        <ccg root="s1_sp9">
          <span id="s1_sp9" begin="4" end="6" category="(S[mod=nm,form=base]\NP[mod=nm,case=ga])\NP[mod=nm,case=o]" rule="&lt;B2" child="s1_sp10 s1_sp11"/>
          <span id="s1_sp10" begin="4" end="5" category="(S[mod=nm,form=cont]\NP[mod=nm,case=ga])\NP[mod=nm,case=o]" terminal="s1_4"/>
          <span id="s1_sp11" begin="5" end="6" category="S[mod=nm,form=base]\S[mod=nm,form=cont]" terminal="s1_5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\y x e.AND(past(e), _ほめる(x, y, e))')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_function_combination_forward(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="とても" pos="副詞-助詞類接続" surf="とても" id="t1_2"/>
          <token base="簡潔" pos="名詞-形容動詞語幹" surf="簡潔" id="t1_3"/>
          <token base="です" katsuyou="基本形" pos="助動詞" surf="です" id="t1_4"/>
        </tokens>
        <ccg root="sp1-5">
          <span child="sp1-6 sp1-7" rule="&gt;B" category="S[mod=nm,form=base]\NP[mod=nm,case=ga]" end="5" begin="2" id="sp1-5"/>
          <span terminal="t1_2" category="S/S" end="3" begin="2" id="sp1-6"/>
          <span child="sp1-8 sp1-9" rule="&lt;B" category="S[mod=nm,form=base]\NP[mod=nm,case=ga]" end="5" begin="3" id="sp1-7"/>
          <span terminal="t1_3" category="S[mod=nm,form=da]\NP[mod=nm,case=ga]" end="4" begin="3" id="sp1-8"/>
          <span terminal="t1_4" category="S[mod=nm,form=base]\S[mod=nm,form=da]" end="5" begin="4" id="sp1-9"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, self.semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'\x._とても(_簡潔(x))')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unary(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unaryChildmatch(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'child0_category' : 'CAT1'}),
                          SemanticRule(r'NP', r'\P.(P & P)', {'child0_category' : 'CAT2'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-2">
          <span terminal="t1_1" category="CAT2" end="2" begin="1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" end="2" begin="1" id="sp1-2"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 & _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unaryChildSurfmatch(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'child0_surf' : '_surfX'}),
                          SemanticRule(r'NP', r'\P.(P & P)', {'child0_surf' : '_surf1'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-2">
          <span terminal="t1_1" category="CAT2" end="2" begin="1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" end="2" begin="1" id="sp1-2"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 & _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unaryChildNomatch(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'child0_category' : 'R'}),
                          SemanticRule(r'NP', r'\P.(P & P)', {'child0_category' : 'T'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 & _base1')
        self.assertNotEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unaryPOSmatchLastUnderespecified(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
                          SemanticRule(r'NP', r'\P.(P & P)', {'child0_pos' : 'NNP'}),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'rule' : 'lex'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-2">
          <span terminal="t1_1" category="N" pos="NNP" end="2" begin="1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" end="2" begin="1" id="sp1-2"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_unaryPOSmatch(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'N', r'\P.P'),
                          SemanticRule(r'NP', r'\P.(P & P)', {'child0_pos' : 'pos1'}),
                          SemanticRule(r'NP', r'\P.(P -> P)', {'child0_pos' : 'xyz'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base1 & _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    # We still need to tell somehow that the third rule is a rule
    # for inner nodes of the CCG tree (and not terminal leaves).
    # Specifying an attribute name that starts by "child" does the job.
    def test_lexical_binary_match_generic(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_binary_specify_left_child(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child0_category' : 'cat1'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_binary_specify_right_child(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child1_category' : 'cat2'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_binary_specify_both_children(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child0_category' : 'cat1',
                                                                 'child1_category' : 'cat2'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_binary_specify_both_childrenNomatch(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child0_category' : 'cat3',
                                                                 'child1_category' : 'cat2'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertNotEqual(expected_semantics, lexpr(semantics))

    def test_match_traverse_2levels(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'cat3', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q & P)', {'rule' : 'lex'}),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)',
                                       {'child0_child0_category' : 'cat1'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
          <token base="base3" pos="pos3" surf="surf3" id="t1_3"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span terminal="t1_3" category="cat3" end="4" begin="3" id="sp1-3"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-4"/>
          <span child="sp1-4 sp1-3" rule="lex" category="NP" end="4" begin="1" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base3 -> (_base2 & _base1)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_match_any(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'cat3', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q & P)', {'rule' : 'lex'}),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child_any_category' : 'cat3'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
          <token base="base3" pos="pos3" surf="surf3" id="t1_3"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span terminal="t1_3" category="cat3" end="4" begin="3" id="sp1-3"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-4"/>
          <span child="sp1-4 sp1-3" rule="lex" category="NP" end="4" begin="1" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base3 -> (_base2 & _base1)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_match_anyCategoryWithFeats(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'XX[case=ga]', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q & P)', {'rule' : 'lex'}),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)',
                                       {'child_any_category' : 'XX'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
          <token base="base3" pos="pos3" surf="surf3" id="t1_3"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" end="3" begin="2" id="sp1-2"/>
          <span terminal="t1_3" category="XX[case=ga]" end="4" begin="3" id="sp1-3"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-4"/>
          <span child="sp1-4 sp1-3" rule="lex" category="NP" end="4" begin="1" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base3 -> (_base2 & _base1)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_match_any2(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'cat3', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q & P)', {'rule' : 'lex'}),
                          SemanticRule(r'NP', r'\P Q.(Q | P)', {'child_any_pos' : 'pos1'}),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child_any_category' : 'cat3'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
          <token base="base3" pos="pos3" surf="surf3" id="t1_3"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" pos="pos1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" pos="pos2" end="3" begin="2" id="sp1-2"/>
          <span terminal="t1_3" category="cat3" pos="pos3" end="4" begin="3" id="sp1-3"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-4"/>
          <span child="sp1-4 sp1-3" rule="lex" category="NP" end="4" begin="1" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base3 -> (_base2 | _base1)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_lexical_binary_surf_any_surf(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'cat2', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)', {'child1_surf' : '_surf2',
                                                                 'child_any_surf' : '_surf1'})]
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
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_inner_node_child_category(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'NP/NP', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)',
                                       {'child1_category' : 'NP/NP'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="NP/NP" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_inner_node_child_categoryWithFeats(self):
        semantic_index = SemanticIndex(None)
        semantic_rules = [SemanticRule(r'cat1', r'\P.P'),
                          SemanticRule(r'NP/NP', r'\P.P'),
                          SemanticRule(r'NP', r'\P Q.(Q -> P)',
                                       {'child1_category' : 'NP/NP'})]
        semantic_index.rules = semantic_rules
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
          <token base="base2" pos="pos2" surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
          <span terminal="t1_2" category="NP/NP[mod=xx]" end="3" begin="2" id="sp1-2"/>
          <span child="sp1-1 sp1-2" rule="lex" category="NP" end="3" begin="1" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_base2 -> _base1')
        self.assertEqual(expected_semantics, lexpr(semantics))

class get_attributes_from_ccg_node_recursivelyTestCase(unittest.TestCase):
    def test_terminal(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token base="base1" pos="pos1" surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-1">
          <span terminal="t1_1" category="cat1" end="2" begin="1" id="sp1-1"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = sentence.find("ccg")
        ccg_root = build_ccg_tree(ccg_tree)
        tokens = sentence.find("tokens")
        attributes = get_attributes_from_ccg_node_recursively(ccg_root, tokens)
        expected_attributes = {'terminal' : 't1_1',
                               'category' : 'cat1',
                               'end' : '2',
                               'begin' : '1',
                               'id' : 'sp1-1',
                               'base' : 'base1',
                               'pos' : 'pos1',
                               'surf' : 'surf1'}
        self.assertEqual(len(expected_attributes), len(attributes))
        for k in expected_attributes:
            self.assertEqual(expected_attributes[k], attributes[k])

    def test_preterminal(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-2">
          <span terminal="t1_1" category="cat1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" id="sp1-2"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = sentence.find("ccg")
        ccg_root = build_ccg_tree(ccg_tree)
        tokens = sentence.find("tokens")
        attributes = get_attributes_from_ccg_node_recursively(ccg_root, tokens)
        expected_attributes = {'category' : 'NP',
                               'rule' : 'lex',
                               'id' : 'sp1-2',
                               'child' : 'sp1-1',
                               'child0_terminal' : 't1_1',
                               'child0_surf' : 'surf1',
                               'child0_category' : 'cat1',
                               'child0_id' : 'sp1-1'}
        self.assertEqual(len(expected_attributes), len(attributes))
        for k in expected_attributes:
            self.assertEqual(expected_attributes.get(k, None), attributes.get(k, None))

    def test_nonterminal1(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token surf="surf1" id="t1_1"/>
        </tokens>
        <ccg root="sp1-3">
          <span terminal="t1_1" category="cat1" id="sp1-1"/>
          <span child="sp1-1" rule="lex" category="NP" id="sp1-2"/>
          <span child="sp1-2" rule="rr" category="NPP" id="sp1-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = sentence.find("ccg")
        ccg_root = build_ccg_tree(ccg_tree)
        tokens = sentence.find("tokens")
        attributes = get_attributes_from_ccg_node_recursively(ccg_root, tokens)
        expected_attributes = {'category' : 'NPP',
                               'rule' : 'rr',
                               'id' : 'sp1-3',
                               'child' : 'sp1-2',
                               'child0_category' : 'NP',
                               'child0_rule' : 'lex',
                               'child0_id' : 'sp1-2',
                               'child0_child' : 'sp1-1',
                               'child0_child0_terminal' : 't1_1',
                               'child0_child0_surf' : 'surf1',
                               'child0_child0_category' : 'cat1',
                               'child0_child0_id' : 'sp1-1'}
        self.assertEqual(len(expected_attributes), len(attributes))
        for k in expected_attributes:
            self.assertEqual(expected_attributes.get(k, None), attributes.get(k, None))

    def test_nonterminal2(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token surf="surf1" id="t1_1"/>
          <token surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" id="sp1-2"/>
          <span child="sp1-1" rule="lex1" category="NP1" id="sp1-3"/>
          <span child="sp1-2" rule="lex2" category="NP2" id="sp1-4"/>
          <span child="sp1-3 sp1-4" rule="rr" category="NPP" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = sentence.find("ccg")
        ccg_root = build_ccg_tree(ccg_tree)
        tokens = sentence.find("tokens")
        attributes = get_attributes_from_ccg_node_recursively(ccg_root, tokens)
        expected_attributes = {'category' : 'NPP',
                               'rule' : 'rr',
                               'id' : 'sp1-5',
                               'child' : 'sp1-3 sp1-4',
                               'child0_category' : 'NP1',
                               'child0_rule' : 'lex1',
                               'child0_id' : 'sp1-3',
                               'child0_child' : 'sp1-1',
                               'child0_child0_terminal' : 't1_1',
                               'child0_child0_surf' : 'surf1',
                               'child0_child0_category' : 'cat1',
                               'child0_child0_id' : 'sp1-1',
                               'child1_category' : 'NP2',
                               'child1_rule' : 'lex2',
                               'child1_id' : 'sp1-4',
                               'child1_child' : 'sp1-2',
                               'child1_child0_terminal' : 't1_2',
                               'child1_child0_surf' : 'surf2',
                               'child1_child0_category' : 'cat2',
                               'child1_child0_id' : 'sp1-2'}
        self.assertEqual(len(expected_attributes), len(attributes),
                         '\n{0}\nvs.\n{1}'.format(expected_attributes, attributes))
        for k in expected_attributes:
            self.assertEqual(expected_attributes.get(k, None), attributes.get(k, None))

    def test_NonterminalButpreterminal(self):
        sentence_str = r"""
      <sentence id="s1">
        <tokens>
          <token surf="surf1" id="t1_1"/>
          <token surf="surf2" id="t1_2"/>
        </tokens>
        <ccg root="sp1-5">
          <span terminal="t1_1" category="cat1" id="sp1-1"/>
          <span terminal="t1_2" category="cat2" id="sp1-2"/>
          <span child="sp1-1" rule="lex1" category="NP1" id="sp1-3"/>
          <span child="sp1-2" rule="lex2" category="NP2" id="sp1-4"/>
          <span child="sp1-3 sp1-4" rule="rr" category="NPP" id="sp1-5"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = sentence.find("ccg")
        ccg_root = build_ccg_tree(ccg_tree)
        tokens = sentence.find("tokens")
        attributes = get_attributes_from_ccg_node_recursively(ccg_root[1], tokens)
        expected_attributes = {'category' : 'NP2',
                               'rule' : 'lex2',
                               'id' : 'sp1-4',
                               'child' : 'sp1-2',
                               'child0_terminal' : 't1_2',
                               'child0_surf' : 'surf2',
                               'child0_category' : 'cat2',
                               'child0_id' : 'sp1-2'}
        self.assertEqual(len(expected_attributes), len(attributes),
                         '\n{0}\nvs.\n{1}'.format(expected_attributes, attributes))
        for k in expected_attributes:
            self.assertEqual(expected_attributes.get(k, None), attributes.get(k, None))

class AssignSemanticsToCCGWithFeatsTestCase(unittest.TestCase):
    def test_np_feature_no(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP', r'\P.P')]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos1" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_pos_equal(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP', r'\P.(P | P)', {'pos' : 'pos1'}),
                                SemanticRule(r'NP', r'\P.(P & P)', {'pos' : 'pos2'})]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos1" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'(_basepred | _basepred)')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_pos_default(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP', r'\P.(P | P)', {'pos' : 'pos1'}),
                                SemanticRule(r'NP', r'\P.(P & P)', {'pos' : 'pos2'})]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos3" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_syntactic_feat(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP[feat1=val1]', r'\P.(P | P)'),
                                SemanticRule(r'NP[feat1=val2]', r'\P.(P & P)')]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos3" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP[feat1=val2]" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred & _basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_syntactic_featSubsume1(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP[feat1=val1]', r'\P.(P | P)'),
                                SemanticRule(r'NP', r'\P.(P & P)')]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos3" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP[feat1=valX]" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred & _basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_syntactic_featSubsume2(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP[feat1=val1]', r'\P.(P | P)'),
                                SemanticRule(r'NP[feat1=val2]', r'\P.(P & P)')]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos3" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP[feat1=val2,feat2=val1]" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred & _basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

    def test_np_feature_syntactic_featNoSubsume(self):
        semantic_index = SemanticIndex(None)
        semantic_index.rules = [SemanticRule(r'NP[feat1=val1]', r'\P.(P | P)'),
                                SemanticRule(r'NP[feat2=val1]', r'\P.(P & P)')]

        sentence_str = r"""
      <sentence id="s0">
        <tokens>
          <token base="basepred" pos="pos3" surf="surfpred" id="t0_0"/>
        </tokens>
        <ccg root="sp0-3">
          <span terminal="t0_0" category="NP" end="1" begin="0" id="sp0-3"/>
        </ccg>
      </sentence>
    """
        sentence = etree.fromstring(sentence_str)
        ccg_tree = assign_semantics_to_ccg(sentence, semantic_index)
        semantics = ccg_tree.get('sem', None)
        expected_semantics = lexpr(r'_basepred')
        self.assertEqual(expected_semantics, lexpr(semantics))

if __name__ == '__main__':
    suite1 = unittest.TestLoader().loadTestsFromTestCase(TypeRaiseTestCase)
    suite2 = unittest.TestLoader().loadTestsFromTestCase(AssignSemanticsToCCGTestCase)
    suite3 = unittest.TestLoader().loadTestsFromTestCase(AssignSemanticsToCCGWithFeatsTestCase)
    suite4 = unittest.TestLoader().loadTestsFromTestCase(
        get_attributes_from_ccg_node_recursivelyTestCase)
    suites = unittest.TestSuite([suite1, suite2, suite3, suite4])
    unittest.TextTestRunner(verbosity=2).run(suites)
