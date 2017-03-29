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

from logic_parser import lexpr
from nltk2coq import normalize_interpretation

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
    suite1  = unittest.TestLoader().loadTestsFromTestCase(Nltk2coqTestCase)
    suites  = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)
