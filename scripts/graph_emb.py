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

from logic_parser import lexpr
from graph_struct import GraphData
from gather_emb import gather3
from gather_emb import gather_output_shape3
seed = 23
np.random.seed(seed=seed)

import tensorflow as tf

import keras.backend as K
from keras import initializers
from keras.models import Model
from keras.layers import Input, Dense, TimeDistributed
from keras.layers import Reshape
from keras.layers import Permute
from keras.layers import RepeatVector
from keras.layers import Flatten
from keras.layers import Add, Multiply
from keras.layers import GlobalMaxPooling1D
from keras.layers.core import Lambda
from keras.layers.embeddings import Embedding
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
# TODO: To debug solutions, we could initialize weights to something easy.
def make_pair_branch(token_emb, max_nodes, max_bi_relations, label='child'):
    embed_dim = 2
    dense_dim = embed_dim
    num_updates = 1

    node_indices = Input(
        shape=(max_nodes,),
        dtype='int32',
        name=label + '_node_inds')
    node_rel = Input(
        shape=(max_nodes, max_bi_relations, 2),
        dtype='int32',
        name=label + '_rel')
    # Weight to compute weighted sum (i.e. average).
    node_rel_weight = Input(
        shape=(max_nodes, max_bi_relations),
        dtype='float32',
        name=label + '_rel_weight')

    node_embs = token_emb(node_indices)
    orig_embs = token_emb(node_indices)
    gathered_embs = gather_layer([orig_embs, node_rel])
    logging.debug('node_embs shape: {0}'.format(node_embs.shape))

    for i in range(num_updates):
        node_embs = tp1_node_update(
            node_embs,
            node_rel,
            node_rel_weight,
            max_nodes,
            max_bi_relations,
            embed_dim,
            label + '_it' + str(i))

    return [node_embs], [node_indices, node_rel, node_rel_weight]
    # return [node_embs, orig_embs, gathered_embs], [node_indices, node_rel, node_rel_weight]

def make_child_parent_branch(token_emb):
    # Normalize summations dividing by the node degree. 
    normalizer = Input(
        shape=(max_nodes, 1),
        dtype='float32',
        name='node_degree')
    child_rel_outputs, child_rel_inputs = make_pair_branch(token_emb, label='child')
    parent_rel_outputs, parent_rel_inputs = make_pair_branch(token_emb, label='parent')
    x = Add(name='child_parent_add')(
        child_rel_outputs + parent_rel_outputs)
    logging.debug('After child parent merge shape: {0}'.format(x.shape))
    logging.debug('normalizer shape: {0}'.format(normalizer.shape))
    x = Multiply(name='child_parent_normalize')([x, normalizer])
    logging.debug('Multiply shape: {0}'.format(x.shape))
    x = GlobalMaxPooling1D()(x)
    outputs = [x]
    inputs = child_rel_inputs + parent_rel_inputs + [normalizer]
    return outputs, inputs

logging.basicConfig(level=logging.DEBUG)
formulas_str = [
    'exists x. pred1(x)',
    'exists y. pred1(y)',
    'exists y. all x. (pred1(y) & pred2(x, y))',
    'exists y. all x. (pred1(y) & pred2(y, x))',
    'exists y. all x. (pred2(y, x) & pred1(y))',
    'exists y. all x. (pred2(y, x) & pred1(y))']
formulas = [lexpr(f) for f in formulas_str]
graph_data = GraphData.from_formulas(formulas)
graph_data.make_matrices()

max_nodes = graph_data.max_nodes
max_bi_relations = graph_data.max_bi_relations
max_tri_relations = graph_data.max_treelets
emb_dim = 2
num_words = graph_data.num_words
logging.debug('Embeddings shape: {0}'.format(graph_data.node_embs.shape))

token_emb = Embedding(
    input_dim=graph_data.num_words,
    output_dim=emb_dim,
    weights=[graph_data.node_embs],
    mask_zero=False, # Reshape layer does not support masking.
    trainable=True,
    name='token_emb')

# outputs, inputs = make_child_parent_branch(token_emb)
outputs, inputs = make_pair_branch(
    token_emb,
    graph_data.max_nodes,
    graph_data.max_bi_relations,
    label='child')

model = Model(inputs=inputs, outputs=outputs)

model.compile(optimizer='rmsprop', loss='categorical_crossentropy', metrics=['accuracy'])

logging.debug('child_node_inds: {0}'.format(graph_data.node_inds.shape))
logging.debug('Birel child normalizer shape: {0}'.format(graph_data.birel_norm.shape))
logging.debug('Birel child normalizer:\n{0}'.format(graph_data.birel_norm))
prediction = model.predict(
    [graph_data.node_inds, graph_data.children, graph_data.birel_norm])
# prediction = model.predict([
#     graph_data.node_inds, graph_data.children, graph_data.node_inds, graph_data.parents, graph_data.birel_norm])
logging.debug('Result:')
logging.debug(prediction.shape)
logging.debug('\n{0}'.format(prediction))

# logging.debug('graph_data.node_embs:')
# logging.debug(graph_data.node_embs.shape)
# logging.debug('\n{0}'.format(graph_data.node_embs))
# 
# logging.debug('graph_data.node_inds:')
# logging.debug(graph_data.node_inds.shape)
# logging.debug('\n{0}'.format(graph_data.node_inds))
# 
# logging.debug('graph_node_embs:')
# logging.debug(graph_node_embs.shape)
# logging.debug('\n{0}'.format(graph_node_embs))
# 
# logging.debug('graph_data.children:')
# logging.debug(graph_data.children.shape)
# logging.debug('\n{0}'.format(graph_data.children))
# 
# logging.debug('gathered_embs:')
# logging.debug(gathered_embs.shape)
# logging.debug('\n{0}'.format(gathered_embs))


