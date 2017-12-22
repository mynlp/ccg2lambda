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
from keras.layers import GlobalMaxPooling1D
from keras.layers.core import Lambda, Flatten
from keras.layers.embeddings import Embedding
from keras.layers.wrappers import Bidirectional
from keras.callbacks import EarlyStopping, ModelCheckpoint, ReduceLROnPlateau, CSVLogger
from keras.regularizers import l2
from keras.layers.normalization import BatchNormalization
from keras.engine.topology import Layer
from keras.layers import Activation

logging.basicConfig(level=logging.DEBUG)

def gather_(data_and_inds):
    data, inds = data_and_inds
    num_rows = data.shape[1]
    num_dims = data.shape[2]
    num_inds = inds.shape[2]
    logging.debug('Indices shape: {0}'.format(inds.shape))
    logging.debug('Data shape: {0}'.format(data.shape))
    logging.debug(inds._keras_shape)
    logging.debug(data._keras_shape)
    data_perm = K.permute_dimensions(data, (1, 2, 0))
    inds_perm = K.permute_dimensions(inds, (1, 2, 0))
    out = K.gather(data_perm, inds_perm)
    out = K.permute_dimensions(out, (4, 2, 0, 1, 3))
    logging.debug(out._keras_shape)
    # out = K.reshape(out, (4, 4, 3, 5))
    # out = K.gather(out, K.arange(2))
    out = K.reshape(out, (4, num_rows, num_inds, num_dims))
    out = K.gather(out, K.arange(batch_size))
    return out

batch_size = 2
factor=2
def gather3(data_and_inds):
    data, inds = data_and_inds
    num_rows = data.shape[1]
    num_dims = data.shape[2]
    num_inds = inds.shape[2]
    logging.debug('Indices shape: {0}'.format(inds.shape))
    logging.debug('Data shape: {0}'.format(data.shape))
    logging.debug(inds._keras_shape)
    logging.debug(data._keras_shape)
    data_perm = K.permute_dimensions(data, (1, 2, 0))
    inds_perm = K.permute_dimensions(inds, (1, 2, 3, 0))
    out = K.gather(data_perm, inds_perm)
    logging.debug(out.shape)
    out = K.permute_dimensions(out, (3, 5, 0, 1, 2, 4))
    logging.debug(out.shape)
    out = K.reshape(out, (batch_size**factor, num_rows, inds.shape[2], inds.shape[-1], data.shape[-1]))
    out = K.gather(out, K.arange(batch_size))
    return out

# TODO: fix this function (but perhaps not necessary for TensorFlow backend).
def gather_output_shape(data_and_inds_shape):
    data_shape, inds_shape = data_and_inds_shape
    num_rows = data_shape[1]
    num_dims = data_shape[2]
    num_inds = inds_shape[2]
    return (batch_size, num_rows, num_inds, num_dims)

def gather_output_shape3(data_and_inds_shape):
    data_shape, inds_shape = data_and_inds_shape
    num_rows = data_shape[1]
    num_dims = data_shape[2]
    num_inds = inds_shape[2]
    return (batch_size**factor, num_rows, inds_shape[2], inds_shape[-1], data_shape[-1])

def make_pair_branch(token_emb, label='child'):
    node_rel = Input(
        shape=(max_nodes, max_bi_relations, 2),
        dtype='int32',
        name=label + '_rel')
    node_indices = Input(
        shape=(max_nodes, 1),
        dtype='int32',
        name=label + '_node_inds')

    node_embs = token_emb(node_indices)
    node_embs = Reshape((max_nodes, 2))(node_embs)
    logging.debug('node_embs shape: {0}'.format(node_embs.shape))
    x = Lambda(gather3, output_shape=gather_output_shape3)([node_embs, node_rel])
    logging.debug('After gather3 shape: {0}'.format(x.shape))
    x = Reshape((max_nodes * max_bi_relations, 2 * 2))(x)
    logging.debug('After gather3-reshape shape: {0}'.format(x.shape))


    # x = token_emb(node_rel)
    # x = Reshape((max_nodes, max_bi_relations, 2 * emb_dim), name=label + '_reshape')(x)
    x = TimeDistributed(
        Dense(4, use_bias=False), name=label + '_dense1')(x)
    logging.debug('After TimeDistributed shape: {0}'.format(x.shape))
    x = BatchNormalization(axis=2, name=label + '_bn1')(x)
    x = Activation('relu')(x)
    x = TimeDistributed(
        Dense(4, use_bias=False), name=label + '_dense2')(x)
    x = BatchNormalization(axis=2, name=label + '_bn2')(x)
    x = Activation('relu')(x)

    x = Reshape((max_nodes, max_bi_relations, 2 * 2))(x)

    logging.debug('Before lambda-sum shape: {0}'.format(x.shape))
    x = Lambda(
        lambda xin: K.sum(xin, axis=2),
        output_shape=(None, max_nodes, emb_dim),
        name=label + '_integrate')(x)
    logging.debug('After lambda-sum axis=1 shape: {0}'.format(x.shape))
    return [x], [node_indices, node_rel]

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

outputs, inputs = make_child_parent_branch(token_emb)

model = Model(inputs=inputs, outputs=outputs)

model.compile(optimizer='rmsprop', loss='categorical_crossentropy', metrics=['accuracy'])

logging.debug('child_node_inds: {0}'.format(graph_data.node_inds.shape))
logging.debug('Actual normalizer: {0}'.format(graph_data.birel_norm.shape))
prediction = model.predict([
    graph_data.node_inds, graph_data.children, graph_data.node_inds, graph_data.parents, graph_data.birel_norm],
    batch_size=batch_size)
logging.debug(prediction.shape)
logging.debug(prediction)


import sys
sys.exit(1)














num_words = 10
word_dim = 3
word_embs = np.random.uniform(size=(num_words, word_dim))

indices_input = Input(shape=(4, 3), dtype='int32')
embs_input = Input(shape=(4, 5), dtype='float32')
node_indices = Input(shape=(4, 1), dtype='int32')

token_emb = Embedding(
    input_dim=num_words,
    output_dim=word_dim,
    weights=[word_embs],
    mask_zero=False, # Reshape layer does not support masking.
    trainable=True,
    name='token_emb')
node_embs = token_emb(node_indices)
node_embs = Reshape((4, 3))(node_embs)
x = Lambda(gather, output_shape=gather_output_shape)([node_embs, indices_input])
x = Reshape((4, 3 * word_dim))(x)
model = Model(inputs=[node_indices, indices_input], outputs=[x])
model.compile(
    optimizer='rmsprop',
    loss='categorical_crossentropy',
    metrics=['accuracy'])

embs = np.array([
    [0.0, 0.0, 0.0, 0.0, 0.0],
    [1.0, 1.0, 1.0, 1.0, 1.0],
    [2.0, 2.0, 2.0, 2.0, 2.0],
    [3.0, 3.0, 3.0, 3.0, 3.0]], dtype='float32')
embs = np.tile(embs, (2, 1, 1))
# embs = np.expand_dims(embs, axis=0)

indices = np.array([
    [[0, 1, 2],
     [1, 2, 3],
     [2, 3, 0],
     [3, 0, 1]],
    [[0, 0, 1],
     [1, 1, 2],
     [2, 2, 3],
     [3, 3, 0]]],
    dtype='int32')
n_indices = np.array([
    [[0],
     [1],
     [2],
     [3]],
    [[3],
     [2],
     [1],
     [0]]],
    dtype='int32')
# indices = np.expand_dims(indices, axis=0)
# indices = np.tile(indices, (2, 1, 1))
out1 = model.predict([n_indices, indices], batch_size=2)
# out2 = model.predict([embs, indices], batch_size=2)
# out = model.predict([embs, indices], batch_size=2)
print(out1)
print(embs.shape)
print(indices.shape)
print(out1.shape)

import sys
sys.exit(1)


from embeddings import DynamicEmbedding

embs = np.array([
    [0.0, 0.0],
    [1.0, 1.0],
    [2.0, 2.0],
    [3.0, 3.0],
    [4.0, 4.0]], dtype='float32')
embs = np.expand_dims(embs, axis=0)
print(embs.shape)

indices_input = Input(shape=(2,), dtype='int32')
embs_input = Input(shape=(5, 2), dtype='float32')

# dyn_embs = Reshape((6, 2))(embs_input)
emb_layer = DynamicEmbedding(embs_input, mode='tensor', dropout=0.0)
x = emb_layer.call(indices_input)

model = Model(inputs=[embs_input, indices_input], outputs=[x])
model.compile(
    optimizer='rmsprop',
    loss='categorical_crossentropy',
    metrics=['accuracy'])

indices = np.array([
    [0, 1],
    [0, 2]],
    dtype='int32')
out = model.predict([embs, indices])
print(out)
print(out.shape)
import sys
sys.exit(1)


embs = np.expand_dims(embs, axis=0)

children = np.zeros((1, 5, 5), dtype='float32')
children[0, 0, 1] = 1
children[0, 0, 3] = 1
children[0, 1, 1] = 1
children[0, 1, 2] = 1
children[0, 2, 3] = 1

indices = np.array([0, 1], dtype='int32').reshape(1,2,1)
print('indices shape: {0}'.format(indices.shape))

# print(children.dot(embs))

children_input = Input(shape=(5, 5))
indices_input = Input(shape=(2,1), dtype='int32')
embs_input = Input(shape=(5, 2))

# x = Dot(axes=(2, 1))([children_input, embs_input])
# def gather(data_and_inds):
#     data, inds = data_and_inds
#     return K.gather(data, inds)
# 
# def gather_output_shape(data_and_inds_shape):
#     data_shape, inds_shape = data_and_inds_shape
#     return data_shape

x  = Lambda(gather, output_shape=gather_output_shape)([embs_input, indices_input])

model = Model(inputs=[embs_input, indices_input], outputs=[x])
model.compile(
    optimizer='rmsprop',
    loss='categorical_crossentropy',
    metrics=['accuracy'])
print(model.predict([embs, indices]))

import sys
sys.exit(1)

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
