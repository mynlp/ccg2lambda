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

import networkx as nx

from logic_parser import lexpr
from nltk2graph import formula_to_graph

# TODO: + test variables vs. constants vs. free variables.
# TODO: + test functions as variables.
# TODO: + test presence of quantifiers.
# TODO: test shared variables and shared constants.
# TODO: + test equalities and other binary operators.
# TODO: + test predicates with two and three variable places.
# TODO: test Japanese characters.
# TODO: test two logical formulas with different proposition order producing the same graph.
# TODO: test two logical formulas with different variable naming producing the same graph.

def nodes_match(attrib1, attrib2):
    return attrib1 == attrib2

def are_graphs_equal(g1, g2):
    return nx.is_isomorphic(g1, g2, node_match=nodes_match)

class Nltk2GraphTestCase(unittest.TestCase):
    def test_constant(self):
        formula = lexpr(r'a')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('a')])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_var(self):
        formula = lexpr(r'x')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('x')])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_pred_var(self):
        formula = lexpr(r'P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('Px')])
        eG.add_edges_from([(0, 1)])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_quant_pred_var(self):
        formula = lexpr(r'exists x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        # from pudb import set_trace; set_trace()
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_quant_pred_var_var(self):
        formula = lexpr(r'exists x y. P(x, y)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'exists', 'y', 'P', 'x', 'y'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3), (2, 4), (4, 5), (4, 6)])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_quantf_pred_var(self):
        formula = lexpr(r'exists P. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'P', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3)])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_lamdba_pred_var(self):
        formula = lexpr(r'\x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['lambda', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        # from pudb import set_trace; set_trace()
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_and_pred_var_pred_var(self):
        formula = lexpr(r'P(x) & Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('&PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

    def test_equality(self):
        formula = lexpr(r'P(x) = Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('=PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

class MergeLeafNodesTestCase(unittest.TestCase):
    def test_constant(self):
        formula = lexpr(r'a')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('a')])
        G = formula_to_graph(formula)
        self.assertTrue(are_graphs_equal(eG, G))

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(Nltk2GraphTestCase)
    suite2  = unittest.TestLoader().loadTestsFromTestCase(MergeLeafNodesTestCase)
    suites  = unittest.TestSuite([suite1, suite2])
    unittest.TextTestRunner(verbosity=2).run(suites)
