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

batch_size = 2
factor=2
def gather3_(data_and_inds):
    data, inds = data_and_inds
    num_rows = data.shape[1]
    num_dims = data.shape[2]
    num_inds = inds.shape[2]
    logging.debug('Indices shape: {0}'.format(inds.shape))
    logging.debug('Data shape: {0}'.format(data.shape))
    logging.debug(inds._keras_shape)
    logging.debug(data._keras_shape)
    logging.debug('gather3 Data:\n{0}'.format(data.value))
    data_perm = K.permute_dimensions(data, (1, 2, 0))
    inds_perm = K.permute_dimensions(inds, (1, 2, 3, 0))
    out = K.gather(data_perm, inds_perm)
    logging.debug(out.shape)
    out = K.permute_dimensions(out, (3, 5, 0, 1, 2, 4))
    logging.debug(out.shape)
    out = K.reshape(out, (batch_size**factor, num_rows, inds.shape[2], inds.shape[-1], data.shape[-1]))
    out = K.gather(out, K.arange(batch_size))
    return out

def gather3(data_and_inds):
    data, inds = data_and_inds
    num_rows = data.shape[1]
    num_dims = data.shape[2]
    num_inds = inds.shape[2]
    feat_dim = tf.shape(data)[-1]
    inds_per_batch = tf.shape(inds)[1] * tf.shape(inds)[2] * tf.shape(inds)[3]
    batch_size = tf.shape(data)[0]
    logging.debug('Indices shape: {0}'.format(inds.shape))
    logging.debug('Data shape: {0}'.format(data.shape))
    logging.debug(inds._keras_shape)
    logging.debug(data._keras_shape)
    data_perm = K.permute_dimensions(data, (1, 2, 0))
    logging.debug('gather3 data_perm shape {0}'.format(data_perm.shape))
    batch_inds = tf.range(0, batch_size)
    batch_inds = tf.reshape(batch_inds, [-1, 1])
    batch_inds = tf.tile(batch_inds, [1, inds_per_batch]) # (2, 12) (batch_size, inds_per_batch)
    batch_inds = tf.reshape(batch_inds, [-1])
    logging.debug('gather3 batch_inds shape {0}'.format(batch_inds.shape))
    indsr = K.reshape(inds, (batch_size, inds_per_batch)) # (2, 12) (batch_size, inds_per_batch)
    indsr = tf.reshape(indsr, [-1])
    indsc = tf.stack([batch_inds, indsr], axis=1)
    logging.debug('gather3 indsc shape {0}'.format(indsc.shape))
    out = tf.gather_nd(data, indsc)
    logging.debug('gather3 out shape {0}'.format(out.shape))
    out = tf.reshape(out, (batch_size, tf.shape(inds)[1], tf.shape(inds)[2], tf.shape(inds)[3], feat_dim))
    return out

def gather_output_shape3(data_and_inds_shape):
    return (2,12,3)

def gather_output_shape3_(data_and_inds_shape):
    data_shape, inds_shape = data_and_inds_shape
    num_rows = data_shape[1]
    num_dims = data_shape[2]
    num_inds = inds_shape[2]
    return (batch_size**factor, num_rows, inds_shape[2], inds_shape[-1], data_shape[-1])

