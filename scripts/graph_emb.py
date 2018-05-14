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

import logging
import numpy as np

from gather import gather3
from gather import gather_output_shape3
seed = 23
np.random.seed(seed=seed)

import keras.backend as K
from keras import initializers
from keras.layers import Input, Dense, TimeDistributed
from keras.layers import Reshape
from keras.layers import Permute
from keras.layers import RepeatVector
from keras.layers import Add, Multiply
from keras.layers import GlobalMaxPooling1D
from keras.layers.core import Lambda
from keras.layers.normalization import BatchNormalization
from keras.layers import Activation

def make_gather_layer():
    return Lambda(gather3, output_shape=gather_output_shape3)

gather_layer = make_gather_layer()

# TODO: make a class and have hyperparameters as class attributes.

def tp1_node_update(graph_node_embs, node_rel, node_rel_weight, max_nodes, max_bi_relations, embed_dim, label):
    """
    graph_node_embs has shape (batch_size, max_nodes per graph, embed_dim feats).
    """
    dense_dim = embed_dim

    x = gather_layer([graph_node_embs, node_rel])
    logging.debug('After gather3 shape: {0}'.format(x.shape))

    x = Reshape((max_nodes * max_bi_relations, 2 * embed_dim))(x)

    x = TimeDistributed(
        Dense(
            dense_dim,
            kernel_initializer=initializers.Ones(),
            bias_initializer=initializers.Zeros(),
            name=label + '_dense1'))(x)
    # TODO: re-enable the batch normalization.
    # x = BatchNormalization(axis=2, name=label + '_bn1')(x)
    x = Activation('relu')(x)
    x = TimeDistributed(
        Dense(
            dense_dim,
            kernel_initializer=initializers.Ones(),
            bias_initializer=initializers.Zeros(),
            name=label + '_dense2'))(x)
    # x = BatchNormalization(axis=2, name=label + '_bn2')(x)
    x = Activation('relu')(x)

    normalizer = Reshape((max_nodes * max_bi_relations,))(node_rel_weight)
    normalizer = RepeatVector(dense_dim)(normalizer)
    normalizer = Permute((2, 1))(normalizer)

    x = Multiply()([x, normalizer])
    x = Reshape((max_nodes, max_bi_relations, dense_dim))(x)

    x = Lambda(
        lambda xin: K.sum(xin, axis=2),
        output_shape=(None, max_nodes * max_bi_relations, dense_dim),
        name=label + '_integrate')(x)
    return x

# TODO: Dense use_bias=True
def make_pair_branch(graph_node_embs, max_nodes, max_bi_relations, label='child'):
    embed_dim = 2
    dense_dim = embed_dim
    num_updates = 1

    node_rel = Input(
        shape=(max_nodes, max_bi_relations, 2),
        dtype='int32',
        name=label + '_rel')
    # Weight to compute weighted sum (i.e. average).
    node_rel_weight = Input(
        shape=(max_nodes, max_bi_relations),
        dtype='float32',
        name=label + '_rel_weight')

    for i in range(num_updates):
        graph_node_embs = tp1_node_update(
            graph_node_embs,
            node_rel,
            node_rel_weight,
            max_nodes,
            max_bi_relations,
            embed_dim,
            label + '_it' + str(i))

    return [graph_node_embs], [node_rel, node_rel_weight]

def make_child_parent_branch(token_emb, max_nodes, max_bi_relations):
    node_indices = Input(
        shape=(max_nodes,),
        dtype='int32',
        name='node_inds')
    graph_node_embs = token_emb(node_indices)

    child_rel_outputs, child_rel_inputs = make_pair_branch(
        graph_node_embs,
        max_nodes,
        max_bi_relations,
        label='child')
    parent_rel_outputs, parent_rel_inputs = make_pair_branch(
        graph_node_embs,
        max_nodes,
        max_bi_relations,
        label='parent')

    x = Add(name='child_parent_add')(
        child_rel_outputs + parent_rel_outputs)
    # Integrate node embeddings into a single graph embedding.
    x = GlobalMaxPooling1D()(x)

    outputs = [x]
    inputs = [node_indices] + child_rel_inputs + parent_rel_inputs
    return outputs, inputs

