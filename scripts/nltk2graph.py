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

from nltk.sem.logic import *
from logic_parser import lexpr

import networkx as nx

import time

node_id_gen = (i for i in range(10000))

def merge_graphs_to(graph, graphs):
    head_node = graph.head_node
    for g in graphs:
        graph = nx.union(graph, g)
        graph.add_edge(head_node, g.head_node)
    graph.head_node = head_node
    return graph

def formula_to_graph(expr):
    if isinstance(expr, str):
        expr = lexpr(expr)
    expr_str = str(expr)
    G = nx.DiGraph()
    if isinstance(expr, ConstantExpression) or \
       isinstance(expr, AbstractVariableExpression) or \
       isinstance(expr, Variable):
        G.head_node = next(node_id_gen)
        G.add_node(G.head_node, label=expr_str)
    elif isinstance(expr, BinaryExpression):
        G.head_node = next(node_id_gen)
        G.add_node(G.head_node, label=expr.getOp())
        graphs = map(formula_to_graph, [expr.first,  expr.second])
        G = merge_graphs_to(G, graphs)
    elif isinstance(expr, ApplicationExpression):
        func, args = expr.uncurry()
        G = formula_to_graph(func)
        args_graphs = map(formula_to_graph, args)
        G = merge_graphs_to(G, args_graphs)
    elif isinstance(expr, VariableBinderExpression):
        quant = '<quant_unk>'
        if isinstance(expr, QuantifiedExpression):
            quant = expr.getQuantifier()
        elif isinstance(expr, LambdaExpression):
            quant = 'lambda'
        G.head_node = next(node_id_gen)
        G.add_node(G.head_node, label=quant)
        var_node_id = next(node_id_gen)
        G.add_node(var_node_id, label=str(expr.variable))
        G.add_edge(G.head_node, var_node_id)
        graphs = map(formula_to_graph, [expr.term])
        G = merge_graphs_to(G, graphs)
    return G

def merge_leaf_nodes(graph, head_node=None):
    """
    Traverses the graph, merging those nodes
    with the same label within the same quantificaton scope.
    """
    pass
