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

from  collections import defaultdict
from nltk.sem.logic import *
from logic_parser import lexpr

import networkx as nx

# class DAG(nx.DiGraph):
#     def __init__(self):
#         super(DAG, self).__init__()
#         self.node_id_gen = (i for i in range(1000000))
# 
#     @staticmethod
#     def from_formula(formula):

node_id_gen = (i for i in range(1000000))

def formula_to_graph(formula, normalize=False):
    """
    Transforms a higher-order formula into a graph, following the paper:
    https://arxiv.org/pdf/1709.09994.pdf
    """
    global node_id_gen
    node_id_gen = (i for i in range(1000000))
    tree = formula_to_tree(formula)
    dag = merge_leaf_nodes(tree)
    dag_renamed = rename_nodes(dag)
    if normalize is True:
        dag_renamed = normalize_graph(dag_renamed)
    return dag_renamed

def guess_head_node(graph):
    if 'head_node' in graph.graph:
        return graph.graph['head_node']
    else:
        assert sum(not list(graph.predecessors(n) for n in graph.nodes())) == 1
        for n in graph.nodes():
            if not list(graph.predecessors(n)):
                return n
    raise(AttributeError(
        'Failed to find head node for graph {0}'.format(graph.graph)))

def make_rooted_graph(graph):
    """
    Create a new root node if it is not already present.
    """
    head_node = guess_head_node(graph)
    # For large graphs, this is very inefficient.
    # We should keep track of the next unassigned node ID.
    root_id = max(graph.nodes()) + 1
    graph.graph['head_node'] = root_id
    graph.add_node(root_id, label='root', type='root')
    graph.add_edge(root_id, head_node)
    return graph

def is_quantifier_node(graph, node_id):
    """
    Returns True if the node in the graph is a quantifier node.
    At the moment, we check whether the label of the node_id
    is 'all' or 'exists', but in the near future we will check
    whether the type of the node is 'quantifier'.
    """
    return graph.node[node_id]['label'] in ['all', 'exists']

def find_predecessor_not_quant(graph, node_id):
    predecessors = [node_id]
    visited = set()
    while predecessors:
        node_id = predecessors.pop()
        if node_id in visited:
            continue
        if get_label(graph, node_id, 'type') != 'quantifier':
            return node_id
        visited.add(node_id)
        new_predecessors = list(reversed(list(graph.predecessors(node_id))))
        predecessors = new_predecessors + predecessors
    raise(ValueError('Predecessor Not Quantifier not found!'))

def get_term_node_from_quant(graph, quant_node):
    assert get_label(graph, quant_node, 'type') == 'quantifier'
    successors = graph.successors(quant_node)
    for s in successors:
        if graph.adj[quant_node][s].get('type', None) != 'var_bind':
            return s
    raise(ValueError('Term successor not found for quantifier.'))

def arrange_quantifiers(graph):
    """
    Collapse all quantifier instances into nodes attached
    to the root.
    """
    head_node = guess_head_node(graph)
    quant_nodes = [n for n in graph.nodes() if is_quantifier_node(graph, n)]
    for qn in quant_nodes:
        # from pudb import set_trace; set_trace()
        pred_not_quant = find_predecessor_not_quant(graph, qn)
        term_node = get_term_node_from_quant(graph, qn)
        graph.add_edge(pred_not_quant, term_node)
        graph.remove_edge(qn, term_node)

        for pred in list(graph.predecessors(qn)):
            graph.remove_edge(pred, qn)
        graph.add_edge(head_node, qn)

    q_dict = defaultdict(list)
    for qn in quant_nodes:
        q_dict[get_label(graph, qn)].append(qn)
    for qn_type, nodes in q_dict.items():
        if len(nodes) > 1:
            master_quant_node = nodes[0]
            for qn in nodes[1:]:
                graph = nx.contracted_nodes(graph, master_quant_node, qn)
    return graph

def remove_constants(graph, constants=None):
    if constants is None:
        constants = ['TrueP']
    for node in list(graph.nodes()):
        if get_label(graph, node) in constants:
            for pred in list(graph.predecessors(node)):
                graph.remove_edge(pred, node)
            graph.remove_node(node)
    return graph

def remove_useless_binary_ops(graph):
    """
    Remove binary operators that only have one child (argument).
    This situations may occur after removing constants. E.g.:
    (P(x) & TrueP) -> (P(x) & ).
    """
    op_nodes = [
        n for n in graph.nodes() \
        if get_label(graph, n, 'type') == 'op' \
        and get_label(graph, n, 'label') != 'not']
    for op_node in op_nodes:
        num_succs = len(list(graph.successors(op_node)))
        if num_succs == 0:
            graph.remove_node(op_node)
        if num_succs == 1:
            parent_nodes = list(graph.predecessors(op_node))
            assert len(parent_nodes) == 1
            child_nodes = list(graph.successors(op_node))
            graph.add_edge(parent_nodes[0], child_nodes[0])
            graph.remove_node(op_node)
    return graph

def normalize_graph(graph):
    """
    This normalization step creates a root node (if not already present),
    attaches to this root node all quantifiers (forall, exists) that are
    declared at the beginning of the formula, and all
    terms of these quantifiers start from the root node.
    Quantifiers that are in other parts of the graph are collapsed into
    the root quantifiers, but their terms are connected to the parents
    of these quantifiers.
    `constants` is a list of constants that will be removed from the graph.
    """
    # 1. Create root node.
    graph = make_rooted_graph(graph)
    # 2. Collapse quantifiers into the root.
    graph = arrange_quantifiers(graph)
    # 3. Remove constants.
    graph = remove_constants(graph)
    # 4. Remove binary operators with only one argument.
    graph = remove_useless_binary_ops(graph)
    return graph

def merge_graphs_to(graph, graphs):
    head_node = graph.graph['head_node']
    for i, g in enumerate(graphs):
        graph = nx.union(graph, g)
        graph.add_edge(head_node, g.graph['head_node'], arg=i)
    graph.graph['head_node'] = head_node
    return graph

def formula_to_tree(expr):
    if isinstance(expr, str):
        expr = lexpr(expr)
    expr_str = str(expr)
    G = nx.DiGraph()
    if isinstance(expr, ConstantExpression) or \
       isinstance(expr, AbstractVariableExpression) or \
       isinstance(expr, Variable):
        G.graph['head_node'] = next(node_id_gen)
        type_str = 'constant' if isinstance(expr, ConstantExpression) else 'variable'
        G.add_node(G.graph['head_node'], label=expr_str, type=type_str)
    elif isinstance(expr, BinaryExpression):
        G.graph['head_node'] = next(node_id_gen)
        G.add_node(G.graph['head_node'], label=expr.getOp(), type='op')
        graphs = map(formula_to_tree, [expr.first,  expr.second])
        G = merge_graphs_to(G, graphs)
    elif isinstance(expr, ApplicationExpression):
        func, args = expr.uncurry()
        G = formula_to_tree(func)
        args_graphs = map(formula_to_tree, args)
        G = merge_graphs_to(G, args_graphs)
    elif isinstance(expr, NegatedExpression):
        G.graph['head_node'] = next(node_id_gen)
        G.add_node(G.graph['head_node'], label='not', type='op')
        graphs = map(formula_to_tree, [expr.term])
        G = merge_graphs_to(G, graphs)
    elif isinstance(expr, VariableBinderExpression):
        quant = '<quant_unk>'
        if isinstance(expr, QuantifiedExpression):
            quant = expr.getQuantifier()
            type = 'quantifier'
        elif isinstance(expr, LambdaExpression):
            quant = 'lambda'
            type = 'binder'
        G.graph['head_node'] = next(node_id_gen)
        G.add_node(G.graph['head_node'], label=quant, type=type)
        var_node_id = next(node_id_gen)
        G.add_node(var_node_id, label=str(expr.variable), type='variable')
        G.add_edge(G.graph['head_node'], var_node_id, type='var_bind')
        graphs = map(formula_to_tree, [expr.term])
        G = merge_graphs_to(G, graphs)
    return G

def get_label_(graph, node_id, label='label', default=None):
    return graph.nodes[node_id].get(label, default)

def get_node_token(graph, node_id):
    token = get_label(graph, node_id, ['surf', 'label'], '<unk>')
    if get_label(graph, node_id, 'type') != 'constant':
        token = '<{0}>'.format(token)
    return token

def get_label(graph, node_id, label='label', default=None):
    if isinstance(label, str):
       return graph.nodes[node_id].get(label, default)
    elif isinstance(label, list):
        for l in label:
            if l in graph.nodes[node_id]:
                return graph.nodes[node_id][l]
    return default

quantifiers = Tokens.QUANTS

def find_its_quantifier(graph, node, label, quant_scope):
    if (node, label) in quant_scope:
        return node
    preds = list(graph.pred[node])
    quants = [find_its_quantifier(graph, pred, label, quant_scope) for pred in preds]
    if not quants or all(q is False for q in quants):
        return False
    return max([q for q in quants if q is not False])

def get_scoped_nodes(graph, head_node=None, quant_active=None, quant_scope=None):
    """
    Returns a dictionary where:
    keys are tuples (scope_node_id, expression) and
    values are lists of tuples (node ID, node_type)s within the scope and with
    the same expression.
    node_type is one of {'leaf', 'internal'}.
    """
    if quant_scope is None:
        quant_scope = {}
    label = get_label(graph, head_node)
    if label in quantifiers:
        quant_active = head_node
    elif quant_active in graph.pred[head_node] and not graph.succ[head_node]:
        # Case: a variable directly attached to its quantifier.
        min_sibling_id = min(list(graph.succ[list(graph.pred[head_node])[0]].keys()))
        assert not graph.succ[min_sibling_id], 'Expected node {0} to be a leaf'.format(head_node)
        quant_scope[(quant_active, label)] = [(head_node, 'leaf')]
    else:
        # Case: a variable quantified in an outer scope.
        node_quantifier = find_its_quantifier(graph, head_node, label, quant_scope)
        if node_quantifier is not False:
            node_type = 'leaf' if not graph.succ[head_node] else 'internal'
            quant_scope[(node_quantifier, label)].append((head_node, node_type))
    for child_node_id in graph.succ[head_node]:
        get_scoped_nodes(graph, child_node_id, quant_active, quant_scope)
    return quant_scope

def merge_leaf_nodes(graph, head_node=None, quant_active=None, quant_scope=None):
    """
    Traverses the graph, merging those nodes
    with the same label within the same quantificaton scope.
    """
    if head_node is None:
        head_node = graph.graph['head_node']
    # Get nodes and their scope information.
    scoped_nodes = get_scoped_nodes(graph, head_node)
    for (quant_node, expr), nodes_to_merge in scoped_nodes.items():
        if len(nodes_to_merge) > 1:
            master_node, node_type = nodes_to_merge[0]
            assert node_type == 'leaf'
            for node, node_type in nodes_to_merge[1:]:
                # Merge leaves within the same scope:
                if node_type == 'leaf':
                    graph = nx.contracted_nodes(graph, master_node, node)
                # Add edges from quantifier to internal function names:
                elif node_type == 'internal':
                    graph.add_edge(quant_node, node)
    graph.graph['head_node'] = head_node
    return graph

def make_label(expr, node_type):
    """
    Make a graph label to replace named variable values and variable functions.
    If it is a variable function (node_type = 'internal'), the label is '<var_func>'.
    If it is a variable value (node_type = 'leaf'), the label is:
        <var_ev> if the variable name starts with 'e' (event).
        <var_en> otherwise (entity).
    """
    label = '<var_en>'
    if node_type == 'internal':
        label = '<var_func>'
    else:
        if expr.startswith('e'):
            label = '<var_ev>'
        if expr[0].isupper():
            label = '<var_func>'
    return label

def rename_nodes(graph, head_node=None, quant_active=None, quant_scope=None):
    """
    Traverses the graph, renaming those nodes that are either
    variable values or variable functions.
    """
    if head_node is None:
        head_node = graph.graph['head_node']
    # Get nodes and their scope information.
    scoped_nodes = get_scoped_nodes(graph, head_node)
    for nodes_to_relabel in scoped_nodes.values():
        for node, node_type in nodes_to_relabel:
            new_label = make_label(
                get_label(graph, node),
                node_type)
            nx.set_node_attributes(graph, {node : new_label}, 'label')
    return graph
