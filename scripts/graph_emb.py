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

import argparse, logging, os
import numpy as np
import pickle

from logic_parser import lexpr
from graph_struct import GraphData
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
from keras.layers import MaxPooling2D, AveragePooling2D, Add, Multiply
from keras.layers.core import Lambda, Flatten
from keras.layers.embeddings import Embedding
from keras.layers.wrappers import Bidirectional
from keras.callbacks import EarlyStopping, ModelCheckpoint, ReduceLROnPlateau, CSVLogger
from keras.regularizers import l2
from keras.layers.normalization import BatchNormalization
from keras.engine.topology import Layer
from keras.layers import Activation

logging.basicConfig(level=logging.INFO)

def make_pair_branch(token_emb, label='child'):
    node_rel = Input(
        shape=(max_nodes, max_bi_relations, 2),
        dtype='int32',
        name=label + '_rel')

    x = token_emb(node_rel)
    x = Reshape((max_nodes, max_bi_relations, 2 * emb_dim), name=label + '_reshape')(x)
    x = TimeDistributed(
        Dense(4), name=label + '_dense1')(x)
    x = BatchNormalization(axis=3, name=label + '_bn1')(x)
    x = Activation('relu')(x)
    x = TimeDistributed(
        Dense(4), name=label + '_dense2')(x)
    x = BatchNormalization(axis=3, name=label + '_bn2')(x)
    x = Activation('relu')(x)

    x = Lambda(
        lambda xin: K.sum(xin, axis=2),
        output_shape=(None, max_nodes, emb_dim),
        name=label + '_integrate')(x)
    return [x], [node_rel]

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
    x = Multiply(name='child_parent_normalize')([x, normalizer])
    outputs = [x]
    inputs = child_rel_inputs + parent_rel_inputs + [normalizer]
    return outputs, inputs

formulas_str = [
    'exists x. pred1(x)',
    'exists y. pred1(y)',
    'exists y. all x. (pred1(y) & pred2(x, y))',
    'exists y. all x. (pred1(y) & pred2(y, x))']
formulas = [lexpr(f) for f in formulas_str]
graph_data = GraphData.from_formulas(formulas)
graph_data.make_matrices()
# print(graph_data.birel_norm)
# print(graph_data.treelets_norm)
# print(graph_data.word2ind)
# import sys
# sys.exit(1)

max_nodes = graph_data.max_nodes
max_bi_relations = graph_data.max_bi_relations
max_tri_relations = graph_data.max_treelets
emb_dim = 2
num_words = graph_data.num_words

# embs_ini = np.array([
#     [0.0, 0.0],
#     [1.0, 1.0],
#     [2.0, 2.0],
#     [3.0, 3.0]])
embs_ini = np.random.uniform(size=num_words * emb_dim).reshape(num_words, emb_dim)
embs_ini[0, :] = [0.0, 0.0]
token_emb = Embedding(
    input_dim=graph_data.num_words,
    output_dim=emb_dim,
    weights=[embs_ini],
    mask_zero=False, # Reshape layer does not support masking.
    trainable=True,
    name='token_emb')
# token_emb = Embedding(
#     input_dim=num_words,
#     output_dim=emb_dim,
#     weights=[embs_ini],
#     mask_zero=False, # Reshape layer does not support masking.
#     trainable=True,
#     name='token_emb')

outputs, inputs = make_child_parent_branch(token_emb)

model = Model(
    inputs=inputs,
    outputs=outputs)

model.compile(
    optimizer='rmsprop',
    loss='categorical_crossentropy',
    metrics=['accuracy'])

# Zero should be reserved for no-relation.
children = np.zeros((1, max_nodes, max_bi_relations, 2), dtype='int32')
children[0, 0, 0, :] = [0, 1] # graph 0, child relation, node 0, 0 -> 1
children[0, 0, 1, :] = [0, 2] # graph 0, child relation, node 0, 0 -> 2
children[0, 1, 0, :] = [1, 2] # graph 0, child relation, node 1, 1 -> 2
children[0, 1, 1, :] = [1, 3] # graph 0, child relation, node 1, 1 -> 3
print(children)

parents = np.zeros((1, max_nodes, max_bi_relations, 2), dtype='int32')
parents[0, 1, 0, :] = [1, 0] # graph 0, parent relation, node 1, 1 -> 0
print(parents)

normalizer = np.ones((1, max_nodes, 1), dtype='float32')
normalizer[0, 0, 0] = 1. / 2
normalizer[0, 1, 0] = 1. / 3

# prediction = model.predict([children, parents, normalizer])
prediction = model.predict([
    graph_data.children, graph_data.parents, graph_data.birel_norm])
print(prediction.shape)
print(prediction)
