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

from collections import defaultdict
from nltk.sem.logic import *
from logic_parser import lexpr

import networkx as nx

class GraphStructures(object):
    """
    For a certain graph, it indexes graph structures for all its nodes.
    """

    def __init__(self, graph):
        self.graph = graph
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
        return

    def collect_structures(self):
        """
        It populates the structure dictionaries.
        """
        # Get children and parent relations.
        for src, trg in self.graph.edges:
            self.children[src].append(trg)
            self.parent[trg].append(src)

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

    def __init__(self, graphs):
        self.graphs = graphs
        self.max_nodes = 20
        self.max_bi_relations = 50
        self.max_tri_relations = 50
        self.word2ind = defaultdict(lambda: len(self.word2ind))
        self.special_tokens = [
            '<unk>', '<exists>', '<all>', '<&>', '<|>',
            '<=>', '<Subj>', '<root>']
        self.word2ind['<unk>'] # index 0 for unknown word.

    def make_vocabulary(self):
        constants = []
        special = []
        for graph in self.graphs:
            for nid in graph.nodes:
                token = get_label(graph, nid, ['surf', 'label'], '<unk>')
                if get_label(graph, nid, 'type') == 'constant':
                    constants.append(token)
                else:
                    special.append('<{0}>'.format(token))
        special = sorted(set(special))
        logging.info('Got {0} special tokens: {1}'.format(len(special), special))
        constants = sorted(set(constants))
        logging.info('Got {0} constant tokens. Some of them are: {1}'.format(
            len(constant), constant[:10]))
        vocab = special + constants
        assert '<unk>' not in vocab
        [self.word2ind[w] for w in vocab]
        return self.word2ind

    # def make_matrix(self, relations, label='label'):

import argparse, logging, os
import numpy as np
import pickle

import chainer

seed = 23
np.random.seed(seed=seed)

import tensorflow as tf
tf.set_random_seed(seed=seed)

import keras
import keras.backend as K
from keras.models import Model
from keras.layers.recurrent import LSTM
from keras.layers import Input, Dropout, Dense, TimeDistributed
from keras.layers import Dot, Permute, Multiply, Concatenate, Reshape
from keras.layers import MaxPooling2D, AveragePooling2D
from keras.layers.core import Lambda, Flatten
from keras.layers.embeddings import Embedding
from keras.layers.wrappers import Bidirectional
from keras.callbacks import EarlyStopping, ModelCheckpoint, ReduceLROnPlateau, CSVLogger
from keras.regularizers import l2

from preprocessing import load_sick_from_xml
from preprocessing import load_nli
from preprocessing import time_count
