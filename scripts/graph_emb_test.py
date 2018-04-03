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
seed = 23
np.random.seed(seed=seed)

from keras.models import Model
from keras.layers.embeddings import Embedding

from graph_emb import make_child_parent_branch

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
logging.debug('Embeddings shape: {0}'.format(graph_data.node_embs.shape))

token_emb = Embedding(
    input_dim=graph_data.node_embs.shape[0],
    output_dim=graph_data.node_embs.shape[1],
    weights=[graph_data.node_embs],
    mask_zero=False, # Reshape layer does not support masking.
    trainable=True,
    name='token_emb')

outputs, inputs = make_child_parent_branch(
    token_emb,
    graph_data.max_nodes,
    graph_data.max_bi_relations)

model = Model(inputs=inputs, outputs=outputs)

model.compile(optimizer='rmsprop', loss='categorical_crossentropy', metrics=['accuracy'])

logging.debug('child_node_inds: {0}'.format(graph_data.node_inds.shape))
logging.debug('Birel child normalizer shape: {0}'.format(graph_data.birel_child_norm.shape))
logging.debug('Birel child normalizer:\n{0}'.format(graph_data.birel_norm))
prediction = model.predict([
    graph_data.node_inds,
    graph_data.children,
    graph_data.birel_child_norm,
    graph_data.parents,
    graph_data.birel_parent_norm])
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


