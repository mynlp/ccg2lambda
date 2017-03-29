#!/usr/bin/python3
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

from copy import deepcopy
from itertools import chain

from nltk import Tree as NLTKTree
from nltk import ImmutableTree


def is_string(variable):
    return isinstance(variable, str)


def get_top(tr):
    """Given a thing that might be a tree or maybe a terminal string, return
    the 'top' of it -- either the node of a tree, or just the string itself."""
    if tr is None:
        return None
    return (tr if is_string(tr) else tr.label())


def tree_contains(tree, subtree):
    tree_is_inst_nltk = isinstance(tree, NLTKTree)
    subtree_is_inst_nltk = isinstance(subtree, NLTKTree)

    # Subtree is a variable, and matches everything.
    subtree_top = get_top(subtree)
    tree_top = get_top(tree)
    if tree_top is None or subtree_top is None:
        return False

    if subtree_top.startswith('?x') and not tree_is_inst_nltk:
        # Get type of the variable.
        var_type = '|'.join(subtree_top.split('|')[1:])
        if var_type == '' or tree_top == var_type:
            return True
        else:
            return False

    # Both are strings and one of them is a QA variable "[]"
    if (not tree_is_inst_nltk and not subtree_is_inst_nltk) and \
       (tree_top == "[]" or subtree_top == "[]"):
        return True

    # tree and subtree are different types, or they have different POS tag,
    # or they have different number of children.
    if tree_is_inst_nltk and not subtree_is_inst_nltk \
       or (not tree_is_inst_nltk and subtree_is_inst_nltk) \
       or (tree_top != subtree_top and subtree_top != "[]") \
       or len(tree) != len(subtree):
        return False

    # Both are strings and equal to each other.
    if (not tree_is_inst_nltk) and tree_top == subtree_top:
        return True

    # Both are trees, and their subtrees are equal.
    for i, src_branch in enumerate(tree):
        trg_branch = subtree[i]
        if not tree_contains(src_branch, trg_branch):
            return False
    return True


def tree_or_string(s):
    """Given a string loaded from the yaml, produce either a Tree or a string,
    if it's just a terminal."""
    if s.startswith(u"("):
        return NLTKTree.fromstring(s)
    return s
