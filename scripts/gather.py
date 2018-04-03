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

import numpy as np
import tensorflow as tf

import keras
import keras.backend as K
from keras.layers.core import Lambda

def gather3(data_and_inds):
    data, inds = data_and_inds
    num_dims = data.shape[2]
    num_inds = inds.shape[2]
    feat_dim = tf.shape(data)[-1]
    inds_per_batch = tf.shape(inds)[1] * tf.shape(inds)[2] * tf.shape(inds)[3]
    batch_size = tf.shape(data)[0]
    data_perm = K.permute_dimensions(data, (1, 2, 0))
    batch_inds = tf.range(0, batch_size)
    batch_inds = tf.reshape(batch_inds, [-1, 1])
    batch_inds = tf.tile(batch_inds, [1, inds_per_batch]) # (2, 12) (batch_size, inds_per_batch)
    batch_inds = tf.reshape(batch_inds, [-1])
    indsr = K.reshape(inds, (batch_size, inds_per_batch)) # (2, 12) (batch_size, inds_per_batch)
    indsr = tf.reshape(indsr, [-1])
    indsc = tf.stack([batch_inds, indsr], axis=1)
    out = tf.gather_nd(data, indsc)
    out = tf.reshape(out, (batch_size, tf.shape(inds)[1], tf.shape(inds)[2], tf.shape(inds)[3], feat_dim))
    return out

def gather_output_shape3(data_and_inds_shape):
    data_shape, inds_shape = data_and_inds_shape
    return (data_shape[0], inds_shape[1], inds_shape[2], inds_shape[3], data_shape[-1])

