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
import tensorflow as tf
from keras.models import Model
from keras.layers import Input
from keras.layers.core import Lambda
from keras.layers.embeddings import Embedding

from gather_emb import gather3
from gather_emb import gather_output_shape3

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
        self.emb_dim = self.embs.shape[1]
        self.token_emb = Embedding(
            input_dim=self.embs.shape[0],
            output_dim=self.emb_dim,
            weights=[self.embs],
            mask_zero=False, # Reshape layer does not support masking.
            trainable=True,
            name='token_emb')
        self.gather_layer = Lambda(gather3, output_shape=gather_output_shape3)

    def make_layer_and_evaluate(self, node_inds, node_rels):
        max_nodes = node_inds.shape[1]
        max_relations = node_rels.shape[2]
        relation_length = node_rels.shape[-1]
        # node_rel specifies node relationships. In case of binary parent-child
        # relations, they are [parent_node, child_node].
        node_rel_input = Input(
            shape=(max_nodes, max_relations, relation_length),
            dtype='int32',
            name='node_rel')
        # Specifies the indices of the dataset node embeddings that are part
        # of the current graph.
        node_inds_input = Input(
            shape=(max_nodes,),
            dtype='int32',
            name='node_inds')

        x = self.token_emb(node_inds_input)
        x = self.gather_layer([x, node_rel_input])
        model = Model(inputs=[node_rel_input, node_inds_input], outputs=[x])
        output = model.predict([node_rels, node_inds])

        batch_size = node_inds.shape[0]
        expected_output_shape = (
            batch_size,
            max_nodes,
            max_relations,
            relation_length,
            self.emb_dim)
        self.assertEqual(expected_output_shape, output.shape,
            msg='Unequal output shape: {0} vs {1}'.format(
            expected_output_shape, output.shape))
        return output

    def test_binary_rel_seq(self):
        node_inds = np.array([[0, 1]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [0, 1]],
             [[1, 0],
              [1, 1]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [0, 0, 0,
             0, 0, 0,
             0, 0, 0,
             1, 10, 100,
             1, 10, 100,
             0, 0, 0,
             1, 10, 100,
             1, 10, 100],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

    def test_binary_rel_noseq(self):
        node_inds = np.array([[1, 3]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [0, 1]],
             [[1, 0],
              [1, 1]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [1, 10, 100,
             1, 10, 100,
             1, 10, 100,
             3, 30, 300,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             3, 30, 300],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

    def test_error_out_of_bounds(self):
        node_inds = np.array([[1, 3]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [1, 1]],
             [[1, 0],
              [1, 2]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        with self.assertRaises(Exception) as context:
            output = self.make_layer_and_evaluate(node_inds, node_rels)
        self.assertTrue('InvalidArgumentError' in str(context.exception))

    def test_binary_rel_max_nodes3(self):
        node_inds = np.array([[1, 3, 4]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [0, 1]],
             [[0, 2],
              [2, 1]],
             [[1, 0],
              [1, 2]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [1, 10, 100,
             1, 10, 100,
             1, 10, 100,
             3, 30, 300,
             1, 10, 100,
             4, 40, 400,
             4, 40, 400,
             3, 30, 300,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             4, 40, 400],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

    def test_binary_rel_max_rel3(self):
        node_inds = np.array([[2, 5]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [0, 1],
              [1, 0]],
             [[1, 0],
              [1, 1],
              [0, 0]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [2, 20, 200,
             2, 20, 200,
             2, 20, 200,
             5, 50, 500,
             5, 50, 500,
             2, 20, 200,
             5, 50, 500,
             2, 20, 200,
             5, 50, 500,
             5, 50, 500,
             2, 20, 200,
             2, 20, 200],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

    def test_ternary(self):
        node_inds = np.array([[1, 3]], dtype='int32')
        node_rels = np.array([
            [[[0, 0, 1],
              [0, 1, 0]],
             [[1, 0, 1],
              [1, 1, 1]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [1, 10, 100,
             1, 10, 100,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             3, 30, 300,
             3, 30, 300,
             3, 30, 300],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

    def test_batch2(self):
        node_inds = np.array([[1, 3], [3, 6]], dtype='int32')
        node_rels = np.array([
            [[[0, 0],
              [0, 1]],
             [[1, 0],
              [1, 1]]],
            [[[1, 0],
              [0, 1]],
             [[1, 1],
              [0, 0]]]],
            dtype='int32')
        assert node_inds.shape[1] == node_rels.shape[1], \
            'Number of nodes must be equal: {0} vs. {1}.'.format(
            node_inds.shape[1], node_rels.shape[1])

        output = self.make_layer_and_evaluate(node_inds, node_rels)
        expected_output = np.array(
            [1, 10, 100,
             1, 10, 100,
             1, 10, 100,
             3, 30, 300,
             3, 30, 300,
             1, 10, 100,
             3, 30, 300,
             3, 30, 300,
             6, 60, 600,
             3, 30, 300,
             3, 30, 300,
             6, 60, 600,
             6, 60, 600,
             6, 60, 600,
             3, 30, 300,
             3, 30, 300],
            dtype='float32').reshape(output.shape)
        self.assertTrue(np.allclose(expected_output, output),
            msg='\nExpected:\n{0}\nGot:\n{1}'.format(expected_output, output))

if __name__ == '__main__':
    suite1 = unittest.TestLoader().loadTestsFromTestCase(GatherTestCase)
    suites = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)

