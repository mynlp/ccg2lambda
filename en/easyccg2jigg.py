#!/usr/bin/python
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

from __future__ import print_function
import argparse
import codecs
from collections import defaultdict
import logging
from lxml import etree
import os
import string
import sys

from nltk import Tree

parser = argparse.ArgumentParser()
parser.add_argument("infile")
parser.add_argument("outfile")
args = parser.parse_args()

logging.basicConfig(level=logging.DEBUG)

def substitute_chars(sin):
  sout = []
  inside_tag = False
  prev_char = None
  for i, s in enumerate(sin):
    if s == '<' and prev_char == '(':
      inside_tag = True
      t = s
    elif s == '>' and (
        prev_char in string.punctuation or \
        prev_char.isupper() or \
        prev_char in string.digits or \
        prev_char == 'j'):
      inside_tag = False
      t = s
    elif inside_tag:
      if s == ' ':
        t = '|||'
      elif s == '(':
        t = '-lb-'
      elif s == ')':
        t = '-rb-'
      else:
        t = s
    else:
      t = s
    sout.append(t)
    prev_char = s
  return ''.join(sout)

def denormalize_category(category):
  return category.replace('-lb-', '(').replace('-rb-', ')')
 
def make_tree(line):
  tree_str = substitute_chars(line.strip())
  # from pudb import set_trace; set_trace()
  try:
    tree = Tree.fromstring(tree_str)
  except ValueError:
    tree = None
    logging.warning('Failed to Tree parse line: {0}'.format(line))
  return tree

def make_tokens_node(tree, sentence_id):
  tokens_node = etree.Element('tokens')
  leaves = [tree[p].label() for p in tree.treepositions() \
    if isinstance(tree[p], Tree) and len(tree[p]) == 0]
  for token_id, leaf in enumerate(leaves):
    token_node = etree.Element('token')
    token_node.set('id', 't{0}_{1}'.format(sentence_id, token_id))
    token_node.set('start', str(token_id))
    attributes = get_attributes(leaf)
    for attr_name, attr_value in attributes.items():
      token_node.set(attr_name, attr_value)
    tokens_node.append(token_node)
  return tokens_node

def get_child_inds(tree, parent=None, i=0, d=None):
  if d is None:
    d = defaultdict(list)
  if isinstance(tree, Tree):
    d[parent].append(i)
  else:
    return i
  next_child = i + 1
  for subtree in tree:
    next_child = get_child_inds(subtree, i, next_child, d)
  return next_child

def get_attributes_from_leaf(node_label):
  try:
    _, cat, word, lemma, pos, ner, _, _ = node_label.split('|||')
  except:
    # from pudb import set_trace; set_trace()
    raise(ValueError(
      ('CCG node {0} with wrong format. '.format(node_label),
       'Expected node_cat_word_lemma_pos_ner_unk1_unk2')))
  cat_norm = \
    denormalize_category(cat).replace(',', '=true,').replace(']', '=true]')
  attributes = {
    'cat' : cat,
    'pos' : pos,
    'entity' : ner,
    'cat' : cat_norm,
    'surf' : word,
    # 'surf' : word.lower(),
    'base' : lemma.lower()}
  return attributes

def get_attributes_from_node(node_label):
  try:
    _, cat, rule, _, _ = node_label.split('|||')
  except:
    raise(ValueError(
      ('CCG node {0} with wrong format. '.format(node_label),
       'Expected unk_cat_rule_unk_unk')))
  cat_norm = \
    denormalize_category(cat).replace(',', '=true,').replace(']', '=true]')
  attributes = {
    'pos' : 'None',
    'rule' : rule,
    'category' : cat_norm}
  return attributes

def get_attributes(node_label):
  """
  From an EasyCCG '_'-normalized node label, it obtains the attributes:
  For leaves: node_cat_word_lemma_pos_ner_unk1_unk2
  For inner nodes: unk_cat_rule_unk_unk
  """
  attributes = {}
  if node_label.startswith('<L'):
    attributes = get_attributes_from_leaf(node_label)
  elif node_label.startswith('<T'):
    attributes = get_attributes_from_node(node_label)
  return attributes

def make_ccg_node(tree, sentence_id, ccg_count=0):
  ccg_node = etree.Element('ccg')
  ccg_node.set('root', 's{0}_sp{1}'.format(sentence_id, 0))
  ccg_node.set('id', 's{0}_ccg{1}'.format(sentence_id, ccg_count))
  nodes = [tree[p] for p in tree.treepositions() \
    if isinstance(tree[p], Tree)]
  child_inds = defaultdict(list)
  get_child_inds(tree, None, 0, child_inds)
  token_id = 0
  for span_id, node in enumerate(nodes):
    span_node = etree.Element('span')
    span_node.set('id', 's{0}_sp{1}'.format(sentence_id, span_id))
    if span_id == 0:
      span_node.set('root', 'true')
    if span_id in child_inds:
      span_node.set('child', ' '.join(
        's{0}_sp{1}'.format(sentence_id, i) for i in child_inds[span_id]))
    attributes = get_attributes(node.label())
    for attr_name, attr_value in attributes.items():
      span_node.set(attr_name, attr_value)
    if len(node) == 0:
      span_node.set('terminal', 't{0}_{1}'.format(sentence_id, token_id))
      span_node.set('category', span_node.get('cat'))
      del span_node.attrib['cat']
      token_id += 1
    ccg_node.append(span_node)
  return ccg_node

def make_jigg_sentence(line, sentence_id):
  r"""
  Given a string of the form:
  (<T S[dcl] ba 1 2> (<L NP This This DT O O NP>) (<T S[dcl]\NP fa 0 2> (<L (S[dcl]\NP)/NP is be VBZ O O (S[dcl]\NP)/NP>) (<T NP lex 0 1> (<T N fa 1 2> (<L N/N John John NNP I-ORG O N/N>) (<L N Walker. Walker. NNP I-ORG O N>) ) ) ) )
  it produces a Jigg old-XML representation of the form:
  <sentence id="s0">
    <tokens>
      <token .../>
      <token .../>
    </tokens>
    <ccg root="s0_sp0" id="s0_ccg0">
      <span id="s0_sp0" .../>
      <span id="s0_sp0" .../>
    </ccg>
  </sentence>
  """
  sentence_id -= 1
  sentence_node = etree.Element('sentence')
  sentence_node.set('id', 's' + str(sentence_id))
  tree = make_tree(line)
  if tree is not None:
    tokens_node = make_tokens_node(tree, sentence_id)
    ccg_node = make_ccg_node(tree, sentence_id)
    sentence_node.append(tokens_node)
    sentence_node.append(ccg_node)
  return sentence_node

def add_ccg_nodes(line, sentence_node, sentence_id, ccg_count):
  sentence_id -= 1
  tree = make_tree(line)
  ccg_node = make_ccg_node(tree, sentence_id, ccg_count)
  sentence_node.append(ccg_node)


root_node = etree.Element('root')
document_node = etree.Element('document')
root_node.append(document_node)
sentences_node = etree.Element('sentences')
document_node.append(sentences_node)

sentence_id = 0
ccg_count = 0
is_new_sentence = False
sentence_tree = None

for line in codecs.open(args.infile, 'r', 'utf-8'):
  if line.startswith('ID='):
    current_sentence_id = int(line.split('=')[-1])
    if sentence_id != current_sentence_id:
      is_new_sentence = True
      sentence_id = current_sentence_id
      ccg_count = 0
      #print("sentence_id:" + str(sentence_id))
    else:
      ccg_count += 1
  else:
    if is_new_sentence:
      is_new_sentence = False
      try:
        sentence_tree = make_jigg_sentence(line, sentence_id)
      except ValueError as e:
        logging.error('Error: {0}.\nLine: {1}'.format(e, line))
        raise
      sentences_node.append(sentence_tree)
    else:
      if sentence_tree is not None:
        add_ccg_nodes(line, sentence_tree, sentence_id, ccg_count)

def serialize_tree(tree):
    tree_str = etree.tostring(
        tree, xml_declaration=True, encoding='utf-8', pretty_print=True)
    return tree_str

root_xml_str = serialize_tree(root_node)
with codecs.open(args.outfile, 'wb') as fout:
    fout.write(root_xml_str)

