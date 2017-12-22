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
from nltk2graph import formula_to_tree
from nltk2graph import merge_leaf_nodes
from nltk2graph import rename_nodes
from nltk2graph import formula_to_graph

# TODO: test Japanese characters.

def are_graphs_equal(g1, g2):
    g1_n2a = nx.get_node_attributes(g1, 'label')
    g1_label_adj = sorted([(g1_n2a[src], frozenset(g1_n2a[trg] for trg in g1.succ[src])) for src in g1.nodes()])
    g2_n2a = nx.get_node_attributes(g2, 'label')
    g2_label_adj = sorted([(g2_n2a[src], frozenset(g2_n2a[trg] for trg in g2.succ[src])) for src in g2.nodes()])

    return g1_label_adj == g2_label_adj

class FormulaToTreeTestCase(unittest.TestCase):
    def assert_graphs_are_equal(self, expected_graph, output_graph):
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
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_var(self):
        formula = lexpr(r'x')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('x')])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_pred_var(self):
        formula = lexpr(r'P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('Px')])
        eG.add_edges_from([(0, 1)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_neg_pred_var(self):
        formula = lexpr(r'-P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['not', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (1, 2)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quant_pred_var(self):
        formula = lexpr(r'exists x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quant_pred_var_var(self):
        formula = lexpr(r'exists x y. P(x, y)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'x', 'exists', 'y', 'P', 'x', 'y'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3), (2, 4), (4, 5), (4, 6)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quantf_pred_var(self):
        formula = lexpr(r'exists P. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', 'P', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_lamdba_pred_var(self):
        formula = lexpr(r'\x. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['lambda', 'x', 'P', 'x'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 3)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_and_pred_var_pred_var(self):
        formula = lexpr(r'P(x) & Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('&PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_tree(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_equality(self):
        formula = lexpr(r'P(x) = Q(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate('=PxQx')])
        eG.add_edges_from([(0, 1),  (0, 3), (1, 2), (3, 4)])
        G = formula_to_tree(formula)
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
        iG.graph['head_node'] = 0

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
        iG.graph['head_node'] = 0

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
        iG.graph['head_node'] = 0

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
        iG.graph['head_node'] = 0

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
        iG.graph['head_node'] = 0

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
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'P', 'x', '&', 'forall', 'Q', 'x'])])
        eG.add_edges_from([(0, 3), (0, 2), (1, 2), (3, 1), (3, 4), (4, 5), (4, 6), (5, 6)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_root_cross(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'P', 'x', '&', 'forall', 'y', 'Q', 'x', 'y'])])
        iG.add_edges_from([(0, 1), (0, 4), (2, 3), (4, 2), (4, 5), (5, 6), (5, 7), (7, 8), (7, 9)])
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'P', 'x', '&', 'forall', 'Q', 'y'])])
        eG.add_edges_from([(0, 3), (0, 2), (1, 2), (3, 1), (3, 4), (4, 5), (4, 6), (5, 2), (5, 6)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

class RenameNodesTestCase(unittest.TestCase):
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
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate('Px')])
        eG.add_edges_from([(0, 1)])

        oG = merge_leaf_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_pred_var_const(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'P', 'y'])])
        iG.add_edges_from([(0, 1), (0, 2), (2, 1), (2, 3)])
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', '<var_en>', 'P', 'y'])])
        eG.add_edges_from([(0, 1), (0, 2), (2, 1), (2, 3)])

        oG = rename_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_pred_var_var(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'forall', 'y', 'P'])])
        iG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 4), (4, 1), (4, 3)])
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', '<var_en>', 'forall', '<var_en>', 'P'])])
        eG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 4), (4, 1), (4, 3)])

        oG = rename_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

    def test_quant_pred_var_var(self):
        iG = nx.DiGraph()
        iG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', 'x', 'forall', 'P', 'P', 'y'])])
        iG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 4), (4, 1), (4, 5)])
        iG.graph['head_node'] = 0

        eG = nx.DiGraph()
        eG.add_nodes_from([
            (i, {'label':s}) for i, s in enumerate(['forall', '<var_en>', 'forall', '<var_func>', '<var_func>', 'y'])])
        eG.add_edges_from([(0, 1), (0, 2), (2, 3), (2, 4), (4, 1), (4, 5)])

        oG = rename_nodes(iG)
        self.assert_graphs_are_equal(eG, oG)

class FormulaToGraphTestCase(unittest.TestCase):
    def assert_graphs_are_equal(self, expected_graph, output_graph):
        self.assertTrue(
            are_graphs_equal(expected_graph, output_graph),
            msg='\nexpected: {0}\n          {1}\nvs.\noutput:   {2}\n          {3}'.format(
                expected_graph.adj, nx.get_node_attributes(expected_graph, 'label'),
                output_graph.adj, nx.get_node_attributes(output_graph, 'label')))
        return

    def assert_graphs_are_different(self, expected_graph, output_graph):
        self.assertFalse(
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
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', '<var_en>', 'P'])])
        eG.add_edges_from([(0, 1), (0,  2), (2, 1)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quant_pred_var_var(self):
        formula = lexpr(r'exists x y. P(x, y)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', '<var_en>', 'exists', '<var_en>', 'P'])])
        eG.add_edges_from([(0, 1), (0, 2), (2,  3), (2, 4), (4, 1), (4, 3)])
        G = formula_to_graph(formula)
        self.assert_graphs_are_equal(eG, G)

    def test_quantf_pred_var(self):
        formula = lexpr(r'exists P. P(x)')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['exists', '<var_func>', '<var_func>', 'x'])])
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

    def test_and_pred_var_pred_var_order(self):
        formula1 = lexpr(r'all x. (P(x) & Q(x))')
        formula2 = lexpr(r'all x. (Q(x) & P(x))')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['all', '<var_en>', '&', 'P', 'Q'])])
        eG.add_edges_from([(0, 1),  (0, 2), (2, 3), (2, 4), (3, 1), (4, 1)])
        G1 = formula_to_graph(formula1)
        G2 = formula_to_graph(formula2)
        self.assert_graphs_are_equal(eG, G1)
        self.assert_graphs_are_equal(eG, G2)

    def test_and_pred_var_pred_var_rename(self):
        formula1 = lexpr(r'all x. (P(x) & Q(x))')
        formula2 = lexpr(r'all y. (Q(y) & P(y))')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['all', '<var_en>', '&', 'P', 'Q'])])
        eG.add_edges_from([(0, 1),  (0, 2), (2, 3), (2, 4), (3, 1), (4, 1)])
        G1 = formula_to_graph(formula1)
        G2 = formula_to_graph(formula2)
        self.assert_graphs_are_equal(eG, G1)
        self.assert_graphs_are_equal(eG, G2)

    def test_and_pred_var_pred_var_rename2(self):
        formula1 = lexpr(r'all x. exists y. (P(x, y) & Q(x))')
        formula2 = lexpr(r'all y. exists x. (Q(y) & P(y, x))')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['all', '<var_en>', 'exists', '<var_en>', '&', 'P', 'Q'])])
        eG.add_edges_from([(0, 1),  (0, 2), (2, 3), (2, 4), (4, 5), (4, 6), (5, 1), (5, 3), (6, 3)])
        G1 = formula_to_graph(formula1)
        G2 = formula_to_graph(formula2)
        self.assert_graphs_are_equal(eG, G1)
        self.assert_graphs_are_equal(eG, G2)

    def test_and_pred_var_pred_var_rename2_different(self):
        formula1 = lexpr(r'all x. exists y. (P(x, y) & Q(x))')
        formula2 = lexpr(r'all y. exists x. (Q(x) & P(x, y))')
        eG = nx.DiGraph()
        eG.add_nodes_from([(i, {'label':s}) for i, s in enumerate(['all', '<var_en>', 'exists', '<var_en>', '&', 'P', 'Q'])])
        eG.add_edges_from([(0, 1),  (0, 2), (2, 3), (2, 4), (4, 5), (4, 6), (5, 1), (5, 3), (6, 3)])
        G1 = formula_to_graph(formula1)
        G2 = formula_to_graph(formula2)
        self.assert_graphs_are_equal(eG, G1)
        # TODO: I cannot test yet for graph differences.
        # self.assert_graphs_are_different(eG, G2)

class NormalizeGraphTestCase(unittest.TestCase):
    def assert_graphs_are_equal(self, expected_graph, output_graph):
        self.assertTrue(
            are_graphs_equal(expected_graph, output_graph),
            msg='\nexpected: {0}\n          {1}\nvs.\noutput:   {2}\n          {3}'.format(
                expected_graph.adj, nx.get_node_attributes(expected_graph, 'label'),
                output_graph.adj, nx.get_node_attributes(output_graph, 'label')))
        return

    def assert_graphs_are_different(self, expected_graph, output_graph):
        self.assertFalse(
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

    def test_quant_swap(self):
        formula1 = lexpr(r'forall x. exists y. P(x, y)')
        formula2 = lexpr(r'exists y. forall x. P(x, y)')
        graph1 = formula_to_graph(formula1, normalize=True)
        graph2 = formula_to_graph(formula2, normalize=True)
        self.assert_graphs_are_equal(graph1, graph2)

    def test_quant_inner(self):
        formula1 = lexpr(r'forall x. (P(x) | exists y. Q(x, y))')
        formula2 = lexpr(r'forall x. exists y. (P(x) | Q(x, y))')
        graph1 = formula_to_graph(formula1, normalize=True)
        graph2 = formula_to_graph(formula2, normalize=True)
        self.assert_graphs_are_equal(graph1, graph2)

    def test_quant2_quant1(self):
        formula1 = lexpr(r'forall x. forall y. exists z. (P(x) & Q(x, y) & R(z))')
        formula2 = lexpr(r'forall x y. exists z. (P(x) & Q(x, y) & R(z))')
        formula3 = lexpr(r'forall x. exists z. forall y. (P(x) & Q(x, y) & R(z))')
        graph1 = formula_to_graph(formula1, normalize=True)
        graph2 = formula_to_graph(formula2, normalize=True)
        graph3 = formula_to_graph(formula3, normalize=True)
        self.assert_graphs_are_equal(graph1, graph2)
        self.assert_graphs_are_equal(graph1, graph3)

# TODO: lexpr(r'P(x) & exists y. Q(x, y)')

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(FormulaToTreeTestCase)
    suite2  = unittest.TestLoader().loadTestsFromTestCase(MergeLeafNodesTestCase)
    suite3  = unittest.TestLoader().loadTestsFromTestCase(RenameNodesTestCase)
    suite4  = unittest.TestLoader().loadTestsFromTestCase(FormulaToGraphTestCase)
    suite5  = unittest.TestLoader().loadTestsFromTestCase(NormalizeGraphTestCase)
    suites  = unittest.TestSuite([suite1, suite2, suite3, suite4, suite5])
    unittest.TextTestRunner(verbosity=2).run(suites)
