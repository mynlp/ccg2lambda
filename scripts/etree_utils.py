# -*- coding: utf-8 -*-
#
#  Copyright 2015 Pascual Martinez-Gomez
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

from lxml import etree

def get_node_at_path(tree, path):
    """
    `tree` is a lxml etree.
    `path` is either a list of indices (integer) or
    a single integer.
    It returns the lxml node of the tree at path `path`.
    """
    assert isinstance(path, list) or isinstance(path, int)
    if isinstance(path, int):
        path = [path]
    node = tree
    for d in path:
        try:
            node = node[d]
        except IndexError:
            raise(IndexError, 'Attempted to index subtree {0} with path {1}'\
                  .format(tree.get('id'), path))
    return node
