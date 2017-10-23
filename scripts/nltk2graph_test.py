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
from nltk2graph import merge_leaf_nodes

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

def are_graphs_equal_(g1, g2):
    return nx.is_isomorphic(g1, g2, node_match=nodes_match)

def are_graphs_equal2(g1, g2):
    g1_graph = nx.convert_node_labels_to_integers(g1)
    g2_graph = nx.convert_node_labels_to_integers(g2)
    if g1_graph.adj != g2_graph.adj:
        return False
    if nx.get_node_attributes(g1_graph, 'label') != nx.get_node_attributes(g2_graph, 'label'):
        return False
    if g1_graph.edges != g2_graph.edges:
        return False
    return True

def are_graphs_equal(g1, g2):
    g1_n2a = nx.get_node_attributes(g1, 'label')
    # from pudb import set_trace; set_trace()
    g1_label_adj = sorted([(g1_n2a[src], frozenset(g1_n2a[trg] for trg in g1.succ[src])) for src in g1.nodes()])
    g2_n2a = nx.get_node_attributes(g2, 'label')
    g2_label_adj = sorted([(g2_n2a[src], frozenset(g2_n2a[trg] for trg in g2.succ[src])) for src in g2.nodes()])

    return g1_label_adj == g2_label_adj

class Nltk2GraphTestCase(unittest.TestCase):
    def assert_graphs_are_equal(self, expected_graph, output_graph):
        # expected_graph = nx.convert_node_labels_to_integers(expected_graph)
        # output_graph = nx.convert_node_labels_to_integers(output_graph)
        # from pudb import set_trace; set_trace()
        self.assertTrue(
            are_graphs_equal(expected_graph, output_graph),
            msg='\nexpected: {0}\n          {1}\nvs.\noutput:   {2}\n          {3}'.format(
                expected_graph.adj, nx.get_node_attributes(expected_graph, 'label'),
                output_graph.adj, nx.get_node_attributes(output_graph, 'label')))
        return

    def test_constant(self):
        formula = lexpr(r'a')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('a')])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_var(self):
        formula = lexpr(r'x')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('x')])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_pred_var(self):
        formula = lexpr(r'P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('Px')])
        eG.add_edges_from([(0, 1)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quant_pred_var(self):
        formula = lexpr(r'exists x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        # from pudb import set_trace; set_trace()
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quant_pred_var_var(self):
        formula = lexpr(r'exists x y. P(x, y)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'exists', 'y', 'P', 'x', 'y'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3), (2, 4), (4, 5), (4, 6)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quantf_pred_var(self):
        formula = lexpr(r'exists P. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'P', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_lamdba_pred_var(self):
        formula = lexpr(r'\x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['lambda', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_and_pred_var_pred_var(self):
        formula = lexpr(r'P(x) & Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('&PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_equality(self):
        formula = lexpr(r'P(x) = Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('=PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

class MergeLeafNodesTestCase(unittest.TestCase):
    def assert_graphs_are_equal(self, expected_graph, output_graph):
        expected_graph = nx.convert_node_labels_to_integers(expected_graph)
        output_graph = nx.convert_node_labels_to_integers(output_graph)
        self.assertTrue(
            are_graphs_equal(expected_graph, output_graph),
            msg='\nexpected: {0}\n          {1}\nvs.\noutput:   {2}\n          {3}'.format(
                expected_graph.adj, nx.get_node_attributes(expected_graph, 'label'),
                output_graph.adj, nx.get_node_attributes(output_graph, 'label')))
        return

    def test_no_quant_pred_var(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('Px')])
        iG.add_edges_from([(0, 1)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('Px')])
        eG.add_edges_from([(0, 1)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_no_quant_pred_var_pred_var(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('&PxQy')])
        iG.add_edges_from([(0, 1), (0, 3), (1, 2), (3, 4)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('&PxQy')])
        eG.add_edges_from([(0, 1), (0, 3), (1, 2), (3, 4)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_no_quant_pred_var_pred_var_same(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('&PxQx')])
        iG.add_edges_from([(0, 1), (0, 3), (1, 2), (3, 2)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('&PxQx')])
        eG.add_edges_from([(0, 1), (0, 3), (1, 2), (3, 4)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_pred_var_pred_var_same(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', '&', 'P', 'x', 'Q', 'x'])])
        iG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 5), (3, 4), (5, 6)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', '&', 'P', 'Q'])])
        eG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 4), (3, 1), (4, 1)])
        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_root_1(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'P', 'x'])])
        iG.add_edges_from([(0, 1), (0, 2), (2, 3)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0, 2), (1, 2)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_root_2(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'P', 'x', '&', 'forall', 'x', 'Q', 'x'])])
        iG.add_edges_from([(0, 1), (0, 4), (2, 3), (4, 2), (4, 5), (5, 6), (5, 7), (7, 8)])
        iG.head_node = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'P', 'x', '&', 'forall', 'Q', 'x'])])
        eG.add_edges_from([(0, 3), (0, 2), (1, 2), (3, 1), (3, 4), (4, 5), (4, 6), (5, 6)])

        # from pudb import set_trace; set_trace()
        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(Nltk2GraphTestCase)
    suite2  = unittest.TestLoader().loadTestsFromTestCase(MergeLeafNodesTestCase)
    suites  = unittest.TestSuite([suite1, suite2])
    unittest.TextTestRunner(verbosity=2).run(suites)
