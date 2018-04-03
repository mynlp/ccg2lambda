# -*- coding: utf-8 -*-
#
#  Copyright 2018 Pascual Martinez-Gomez
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

from collections import Counter
from collections import defaultdict
import itertools
import logging
import numpy as np

from nltk2graph import formula_to_graph
from nltk2graph import get_label
from nltk2graph import get_node_token

import networkx as nx

# TODO: node id 0 should be reserved for "no node".

class GraphStructures(object):
    """
    For a certain graph, it indexes graph structures for all its nodes.
    """

    def __init__(self, graph):
        self.graph = nx.convert_node_labels_to_integers(graph, first_label=1)
        # Child nodes.
        self.children = defaultdict(list)
        # Parent nodes.
        self.parents = defaultdict(list)
        # Treelets where the current node participates as the predicate.
        self.treelets_predicate = defaultdict(list)
        # Treelets where the current node participates as the left child.
        self.treelets_left = defaultdict(list)
        # Treelets where the current node participates as the right child.
        self.treelets_right = defaultdict(list)
        self.collect_structures()
        return

    def collect_structures(self):
        """
        It populates the structure dictionaries.
        """

        # Get children and parent relations.
        for src, trg in self.graph.edges:
            self.children[src].append(trg)
            self.parents[trg].append(src)

        # Get treelet relations.
        for nid in self.graph.nodes:
            if get_label(self.graph, nid, 'type') == 'constant':
                succs = list(self.graph.successors(nid))
                succs.sort(key=lambda x: get_label(self.graph, x, 'arg', 0))
                combs = itertools.combinations(succs, 2)
                for left, right in combs:
                    self.treelets_predicate[nid].append((left, right))
                    self.treelets_left[left].append((nid, right))
                    self.treelets_right[right].append((left, nid))
        return

class GraphData(object):
    """
    Manages multiple graphs and transforms them into matrices
    for deep learning.
    """

    def __init__(self, graph_structs):
        self.graph_structs = graph_structs
        self._max_nodes = None
        self._max_bi_relations = None
        self._max_treelets = None
        self.word2ind = defaultdict(lambda: len(self.word2ind))
        self.special_tokens = [
            '<unk>', '<exists>', '<all>', '<&>', '<|>',
            '<=>', '<Subj>', '<root>']
        self.word2ind['<unk>'] # index 0 for unknown word.
        self.emb_dim = 2
        self.node_embs = None
        self.node_inds = None
        self._max_nodes = self.max_nodes
        self._max_bi_relations = self.max_bi_relations
        self._max_treelets = self.max_treelets
        logging.info('Max nodes: {0}'.format(self._max_nodes))
        logging.info('Max bi-relations: {0}'.format(self._max_bi_relations))
        logging.info('Max treelets: {0}'.format(self._max_treelets))

        self.children = None
        self.parents = None
        self.treelets_predicate = None
        self.treelets_right = None
        self.treelets_left = None

        self.birel_norm = None
        self.treelets_norm = None

    def copy_parameters(self, graph_data):
        assert isinstance(graph_data, self.__class__)
        self._max_nodes = graph_data._max_nodes
        self._max_bi_relations = graph_data._max_bi_relations
        self._max_treelets = graph_data._max_treelets
        self.word2ind = graph_data.word2ind

    @staticmethod
    def from_formulas(formulas):
        graphs = [formula_to_graph(formula, normalize=True) for formula in formulas]
        graph_structs = [GraphStructures(g) for g in graphs]
        return GraphData(graph_structs)

    @property
    def max_nodes(self):
        # TODO: compute other statistics.
        return max(len(gs.graph.nodes) for gs in self.graph_structs) + 1

    @property
    def num_words(self):
        # TODO: compute other statistics.
        return len(self.word2ind)

    @property
    def max_bi_relations(self):
        max_children = max(
            len(chs) for gs in self.graph_structs for chs in gs.children.values())
        max_parents = max(
            len(prs) for gs in self.graph_structs for prs in gs.parents.values())
        return max(max_children, max_parents)

    @property
    def max_treelets(self):
        return max(len(treelets) for gs in self.graph_structs for treelets in itertools.chain(
            gs.treelets_predicate.values(),
            gs.treelets_right.values(),
            gs.treelets_left.values()))

    def make_vocabulary(self):
        counter = Counter()
        constants = []
        special = []
        for gs in self.graph_structs:
            graph = gs.graph
            for nid in graph.nodes:
                token = get_node_token(graph, nid)
                if get_label(graph, nid, 'type') == 'constant':
                    constants.append(token)
                    counter[token] += 1
                else:
                    special.append(token)
                    counter[token] += 1
        logging.info('Most common 10 tokens: {0}'.format(counter.most_common()[:10]))
        special = sorted(set(special))
        logging.info('Got {0} special tokens: {1}'.format(len(special), special))
        constants = sorted(set(constants))
        logging.info('Got {0} constant tokens. Some of them are: {1}'.format(
            len(constants), constants[:10]))
        vocab = special + constants
        assert '<unk>' not in vocab
        [self.word2ind[w] for w in vocab]
        self.word2emb = np.random.uniform(size=(len(self.word2ind), 2))
        return self.word2ind

    # TODO: guard against index-out-of-bounds error when preparing trial and
    # test matrices.
    def make_birel_matrix(self, relation='children'):
        birel = np.zeros((
            len(self.graph_structs),
            self._max_nodes,
            self._max_bi_relations,
            2),
            dtype='int32')
        for i, gs in enumerate(self.graph_structs):
            for j, nid in enumerate(gs.graph.nodes):
                nid_token = get_node_token(gs.graph, nid)
                for k, rel_nid in enumerate(getattr(gs, relation)[nid]):
                    rel_token = get_node_token(gs.graph, rel_nid)
                    try:
                        # birel[i, j, k, :] = [nid_token, rel_token]
                        birel[i, j, k, :] = [nid, rel_nid]
                    except IndexError:
                        continue
        return birel

    # TODO: remove word2ind mapping.
    def make_treelet_matrix(self, relation='treelet_predicate'):
        treelets = np.zeros((
            len(self.graph_structs),
            self._max_nodes,
            self._max_treelets,
            3),
            dtype='int32')
        for i, gs in enumerate(self.graph_structs):
            for j, nid in enumerate(gs.graph.nodes):
                nid_token = get_node_token(gs.graph, nid)
                for k, (rel1_nid, rel2_nid) in enumerate(getattr(gs, relation)[nid]):
                    rel1_token = get_node_token(gs.graph, rel1_nid)
                    rel2_token = get_node_token(gs.graph, rel2_nid)
                    treelets[i, j, k, :] = [
                        self.word2ind[nid_token],
                        self.word2ind[rel1_token],
                        self.word2ind[rel2_token]]
        return treelets

    def make_birel_normalizers(self, relation='children'):
        birel_norm = np.zeros((
            len(self.graph_structs),
            self._max_nodes,
            self._max_bi_relations),
            dtype='float32')
        for i, gs in enumerate(self.graph_structs):
            for j, nid in enumerate(gs.graph.nodes):
                degree = len(gs.children[nid]) + len(gs.parents[nid])
                rel_degree = len(getattr(gs, relation)[nid])
                for k in range(rel_degree):
                    birel_norm[i, j, k] = 1. / degree
        return birel_norm
            
    def make_treelets_normalizers(self):
        treelets_norm = np.ones((
            len(self.graph_structs),
            self._max_nodes,
            1),
            dtype='float32')
        for i, gs in enumerate(self.graph_structs):
            for j, nid in enumerate(gs.graph.nodes):
                num_treelets = sum([
                    len(getattr(gs, 'treelets_' + d)[nid]) for d in ['predicate', 'right', 'left']])
                if num_treelets == 0.0:
                    treelets_norm[i, j, 0] = 0.0
                else:
                    treelets_norm[i, j, 0] = 1. / num_treelets
        return treelets_norm

    def make_node_inds(self):
        node_inds = np.zeros((
            len(self.graph_structs),
            self._max_nodes),
            dtype='float32')
        for i, gs in enumerate(self.graph_structs):
            for j, nid in enumerate(gs.graph.nodes):
                node_token = get_node_token(gs.graph, nid)
                node_inds[i, nid] = self.word2ind[node_token]
        return node_inds

    def make_node_embeddings(self):
        # embeddings = np.random.uniform(size=(
        #     len(self.word2ind), self.emb_dim))
        embeddings = np.array(range(len(self.word2ind) * self.emb_dim), dtype='float32').reshape(
            len(self.word2ind), self.emb_dim) * 100
        # embeddings[self.word2ind['<&>'], :] *= 100
        embeddings[0, :] *= 0.0
        # embeddings[self.word2ind['<unk>'], :] *= 0
        return embeddings

    def make_matrices(self):
        # Populates self.word2ind
        self.make_vocabulary()

        self.node_embs = self.make_node_embeddings()
        self.node_inds = self.make_node_inds()
        # Makes relations between pairs of nodes (children and parents).
        self.children = self.make_birel_matrix(relation='children')
        self.parents = self.make_birel_matrix(relation='parents')

        # Makes relations between three nodes (treelets).
        self.treelets_predicate = self.make_treelet_matrix(relation='treelets_predicate')
        self.treelets_right = self.make_treelet_matrix(relation='treelets_right')
        self.treelets_left = self.make_treelet_matrix(relation='treelets_left')

        # Makes normalizers (numbers between 0 and 1) to weight the sum
        # and obtain average embeddings.
        self.birel_child_norm = self.make_birel_normalizers(relation='children')
        self.birel_parent_norm = self.make_birel_normalizers(relation='parents')
        self.treelets_norm = self.make_treelets_normalizers()
        return None

