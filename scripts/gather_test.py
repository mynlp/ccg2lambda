#!/usr/bin/python3
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

import unittest

import numpy as np

seed = 23
np.random.seed(seed=seed)

import tensorflow as tf
tf.set_random_seed(seed=seed)

import keras
from keras.models import Model
from keras.layers import Input
from keras.layers.core import Lambda
from keras.layers.embeddings import Embedding

from gather_emb import gather3
from gather_emb import gather3_output_shape3

# TODO: change max_nodes, max_bi_relations and the expressiveness of relations (bi, tri).
class GatherTestCase(unittest.TestCase):
    def setUp(self):
        self.embs = np.array([
            [0, 0, 0],
            [1, 10, 100],
            [2, 20, 200],
            [3, 30, 300],
            [4, 40, 400],
            [5, 50, 500],
            [6, 60, 600],
            [7, 70, 700],
            [8, 80, 800],
            [9, 90, 900]],
            dtype='float32')
        self.token_emb = Embedding(
            input_dim=embs.shape[0],
            output_dim=embs.shape[1],
            weights=[embs],
            mask_zero=False, # Reshape layer does not support masking.
            trainable=True,
            name='token_emb')

    def test_binary_rel(self):
        max_nodes = 3
        max_bi_relations = 2
        # node_rel specifies node relationships. In case of binary parent-child
        # relations, they are [parent_node, child_node].
        node_rel = Input(
            shape=(max_nodes, max_bi_relations, 2),
            dtype='int32',
            name='node_rel')
        # Specifies the indices of the dataset node embeddings that are part
        # of the current graph.
        node_inds = Input(
            shape=(max_nodes,),
            dtype='int32',
            name='node_inds')
        x = self.token_emb(node_inds)
        x = Lambda(gather3, output_shape=gather_output_shape3)([x, node_rel])
        model = Model(inputs=[node_rel, node_inds], outputs=[x])
        
        uinds = np.array([
            [0,1,2],
            [5,6,7]], dtype='int32')
        
        inds = np.array([
            [[[0, 1],
              [1, 2]],
             [[1, 1],
              [2, 2]],
             [[2, 2],
              [2, 2]]],
            [[[1, 2],
              [0, 0]],
             [[0, 0],
              [0, 0]],
             [[0, 0],
              [1, 2]]]],
            dtype='int32')
        
        print('Inds shape: {0}'.format(inds.shape))
        output = model.predict([inds, uinds])
        print(output)
        print(output.shape)

        self.assertEqual(expected_relations, relations)

if __name__ == '__main__':
    suite1 = unittest.TestLoader().loadTestsFromTestCase(GatherTestCase)
    suites = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)

