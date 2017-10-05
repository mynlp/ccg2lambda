#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez
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

from coq_analyzer import get_tree_pred_args
from coq_analyzer import get_premises_that_match_conclusion_args
from tree_tools import tree_or_string

class GetTreePredArgsTestCase(unittest.TestCase):
    def test_premise_one_var(self):
        coq_line = 'H2 : _kiss x1'
        expected_args = tree_or_string('x1')
        args = get_tree_pred_args(coq_line)
        self.assertEqual(expected_args, args)

    def test_premise_zero_var(self):
        coq_line = 'H2 : True'
        expected_args = None
        args = get_tree_pred_args(coq_line)
        self.assertEqual(expected_args, args)

    def test_premise_case_var(self):
        coq_line = 'H2 : _woman (Acc x1)'
        expected_args = tree_or_string('(Acc x1)')
        args = get_tree_pred_args(coq_line)
        self.assertEqual(expected_args, args)

class GetPremisesThatMatchConclusionArgsTestCase(unittest.TestCase):
    def test_one_casevar_one_prem_match(self):
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_person (Acc x1)"
        expected_premises = [
            "H0 : _woman (Acc x1)"]
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_casevar_zero_prem_match(self):
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_person (Acc x2)"
        expected_premises = []
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_casevar_zero_prem_match2(self):
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_person (Ind x1)"
        expected_premises = []
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_var_one_prems_match(self):
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_greets x1"
        expected_premises = [
            "H2 : _kiss x1"]
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_var_zero_prems_match(self):
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_greets x2"
        expected_premises = []
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_anonvar_one_prems_match(self):
        # Use anonymous variables (e.g. ?284 in the conclusion) to match
        # any variable in the premises.
        premise_lines = [
            "H2 : _kiss x1",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_greets ?284"
        expected_premises = ["H2 : _kiss x1"]
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

    def test_one_anonvar_two_prems_match(self):
        # Use anonymous variables (e.g. ?284 in the conclusion) to match
        # any case-constrained variable in the premises.
        premise_lines = [
            "H2 : _kiss x1",
            "H : _bird (Subj x2)",
            "H : _man (Subj x1)",
            "H0 : _woman (Acc x1)"]
        conclusion_line = "_greets (Subj ?284)"
        expected_premises = [
            "H : _bird (Subj x2)",
            "H : _man (Subj x1)"]
        matching_premises = get_premises_that_match_conclusion_args(
            premise_lines, conclusion_line)
        self.assertEqual(expected_premises, matching_premises)

if __name__ == '__main__':
    suite1 = unittest.TestLoader().loadTestsFromTestCase(GetTreePredArgsTestCase)
    suite2 = unittest.TestLoader().loadTestsFromTestCase(
        GetPremisesThatMatchConclusionArgsTestCase)
    suites = unittest.TestSuite([suite1, suite2])
    unittest.TextTestRunner(verbosity=2).run(suites)
