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

from collections import defaultdict
import itertools
from itertools import chain, product
import logging
import re

from linguistic_tools import linguistic_relationship
from normalization import denormalize_token, normalize_token

def get_tokens_from_ccg_tree(ccg_xml_tree):
    tokens = [denormalize_token(t) for t in ccg_xml_tree.xpath('//token/@base')]
    return tokens

def create_antonym_axioms(relations_to_pairs):
    """
    For every linguistic relationship, check if 'antonym' is present.
    If it is present, then create an entry named:
    Axiom ax_antonym_token1_token2 : forall x, _token1 x -> _token2 x -> False.
    """
    relation = 'antonym'
    antonyms = relations_to_pairs[relation]
    axioms = []
    if not antonyms:
        return axioms
    for t1, t2 in antonyms:
        axiom = 'Axiom ax_{0}_{1}_{2} : forall x, _{1} x -> _{2} x -> False.'\
                .format(relation, t1, t2)
        axioms.append(axiom)
    return axioms

def get_lexical_relations(doc):
    # Get tokens from all CCG trees and de-normalize them.
    # (e.g. remove the preceding underscore).
    tokens = doc.xpath('//token/@base')
    # For every token pair, extract linguistic relationships.
    relations_to_pairs = defaultdict(list)
    token_pairs = list(itertools.product(tokens, tokens))
    for i, (t1, t2) in enumerate(token_pairs):
        if t1 == t2:
            continue
        # Exclude symmetrical relationships.
        if (t2, t1) in token_pairs[:i]:
            continue
        relations = linguistic_relationship(t1, t2)
        for relation in relations:
            relations_to_pairs[relation].append((t1, t2))
    # For every linguistic relationship, check if 'antonym' is present.
    # If it is present, then create an entry named:
    # Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x -> False.
    antonym_axioms = create_antonym_axioms(relations_to_pairs)
    # Return the axioms as a list.
    axioms = list(itertools.chain(*[antonym_axioms]))
    return list(set(axioms))






def GetTokensFromCCGTree(ccg_xml_tree):
  tokens_node = ccg_xml_tree.find('.//tokens')
  tokens = [token.get('base') for token in tokens_node]
  for i in range(len(tokens)):
    tokens[i] = re.sub(r'DOT', r'.', tokens[i])
    tokens[i] = re.sub(r'COMMA', r',', tokens[i])
    if tokens[i].startswith('_'):
      tokens[i] = tokens[i][1:]
  return tokens

def FindLinguisticRelations(relation, relations_to_pairs, pred_args=None):
  """
  Return the necessary parameters to build axioms. These parameters
  will come in a list of tuples, where each tuple is:
  (relation, pred1, pred2, longest_args, pred1_args, pred2_args)
  """
  if pred_args is None:
    pred_args = defaultdict(lambda: ['x'])
  ling_relations = relations_to_pairs[relation]
  relations = []
  if not ling_relations:
    return relations
  for t1, t2 in ling_relations:
    t1_args = pred_args[t1]
    t2_args = pred_args[t2]
    longest_args = t1_args if len(t1_args) >= len(t2_args) else t2_args
    relations.append(
      (relation, t1, t2, longest_args, t1_args, t2_args))
  return relations

def CreateAntonymAxioms(relations_to_pairs, pred_args=None):
  """
  For every linguistic relationship, check if 'antonym' is present.
  If it is present, then create an entry named:
  Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x -> False.
  """
  axioms = []
  relations = FindLinguisticRelations('antonym', relations_to_pairs, pred_args)
  for (rel, pred1, pred2, longest_args, pred1_args, pred2_args) in relations:
    axiom = 'Axiom ax_{0}_{1}_{2} : forall {3}, {1} {4} -> {2} {5} -> False.'\
            .format(rel, pred1, pred2, ' '.join(longest_args),
                    ' '.join(pred1_args), ' '.join(pred2_args))
    axioms.append(axiom)
  return axioms

def CreateSynonymAxioms(relations_to_pairs, pred_args):
  axioms = []
  relations = FindLinguisticRelations('synonym', relations_to_pairs, pred_args)
  for (rel, pred1, pred2, longest_args, pred1_args, pred2_args) in relations:
    axiom = 'Axiom ax_{0}_{1}_{2} : forall {3}, _{1} {4} -> _{2} {5}.'\
            .format(rel, pred1, pred2, ' '.join(longest_args),
                    ' '.join(pred1_args), ' '.join(pred2_args))
    axioms.append(axiom)
  return axioms

def CreateHypernymAxioms(relations_to_pairs, pred_args):
  axioms = []
  relations = FindLinguisticRelations('hypernym', relations_to_pairs, pred_args)
  for (rel, pred1, pred2, longest_args, pred1_args, pred2_args) in relations:
    axiom = 'Axiom ax_{0}_{1}_{2} : forall {3}, _{1} {4} -> _{2} {5}.'\
            .format(rel, pred1, pred2, ' '.join(longest_args),
                    ' '.join(pred1_args), ' '.join(pred2_args))
    axioms.append(axiom)
  return axioms

def CreateHyponymAxioms(relations_to_pairs, pred_args):
  axioms = []
  relations = FindLinguisticRelations('hyponym', relations_to_pairs, pred_args)
  for (rel, pred1, pred2, longest_args, pred1_args, pred2_args) in relations:
    axiom = 'Axiom ax_{0}_{1}_{2} : forall {3}, _{2} {4} -> _{1} {5}.'\
            .format(rel, pred1, pred2, ' '.join(longest_args),
                    ' '.join(pred1_args), ' '.join(pred2_args))
    axioms.append(axiom)
  return axioms

def CreateSiblingAxioms(relations_to_pairs):
  """
  For every linguistic relationship, check if 'sibling' is present.
  If it is present, then create an entry named:
  Axiom ax_sibling_token1_token2 : forall x, _token1 x -> _token2 x -> False.
  """
  raise NotImplemented('No adaptation of these axioms to new abduction')
  relation = 'sibling'
  siblings = relations_to_pairs[relation]
  axioms = []
  if not siblings:
    return axioms
  for t1, t2 in siblings:
    axiom = 'Axiom ax_{0}_{1}_{2} : forall x, _{1} x -> _{2} x -> False.'\
            .format(relation, t1, t2)
    axioms.append(axiom)
  return axioms

def GetApproxRelationsFromPreds(premise_preds, conclusion_pred, threshold=0.8):
  import gensim
  model = gensim.models.Word2Vec.load_word2vec_format(
    './GoogleNews-vectors-negative300.bin', binary=True)
  src_preds = [normalize_token(p) for p in premise_preds]
  trg_pred = normalize_token(conclusion_pred)

  approx_simil = []
  for src_pred in src_preds:
    if src_pred == trg_pred:
      continue
    similarity = model.similarity(src_pred, trg_pred)
    approx_simil.append((similarity, src_pred))
  approx_simil_sorted = sorted(approx_simil, key=lambda x: x[0], reverse=True)
  if approx_simil_sorted[0][0] < threshold:
    return []
  best_pred = approx_simil_sorted[0][1]
  axioms = ['Axiom ax_{0}_{1}_{2} : forall x, _{1} x -> _{2} x.'\
            .format('approx', best_pred, trg_pred)]
  return axioms

def GetLexicalRelationsFromPreds(premise_preds, conclusion_pred, pred_args=None):
  # src_preds = [normalize_token(p) for p in premise_preds]
  # trg_pred = normalize_token(conclusion_pred)
  # from pudb import set_trace; set_trace()
  src_preds = [denormalize_token(p) for p in premise_preds]
  trg_pred = denormalize_token(conclusion_pred)

  relations_to_pairs = defaultdict(list)

  for src_pred in src_preds:
    if src_pred == trg_pred or \
       src_pred in '_False' or \
       src_pred in '_True':
      continue
    relations = LinguisticRelationship(src_pred, trg_pred)
    src_pred_norm = normalize_token(src_pred)
    trg_pred_norm = normalize_token(trg_pred)
    for relation in relations:
      relations_to_pairs[relation].append((src_pred_norm, trg_pred_norm))
  antonym_axioms = CreateAntonymAxioms(relations_to_pairs, pred_args)
  synonym_axioms = CreateSynonymAxioms(relations_to_pairs, pred_args)
  hypernym_axioms = CreateHypernymAxioms(relations_to_pairs, pred_args)
  hyponym_axioms = CreateHyponymAxioms(relations_to_pairs, pred_args)
  # sibling_axioms = CreateSiblingAxioms(relations_to_pairs)
  # Return the axioms as a list.
  # axioms = list(chain(*[antonym_axioms, synonym_axioms, hypernym_axioms,
  #                       hyponym_axioms, sibling_axioms]))
  axioms = antonym_axioms + synonym_axioms + hypernym_axioms + hyponym_axioms
  return list(set(axioms))

def GetLexicalRelations(ccg_xml_trees):
  # from pudb import set_trace; set_trace()
  # Get tokens from all CCG trees and de-normalize tokens
  # (e.g. remove the preceding underscore).
  tokens = list(chain(*[GetTokensFromCCGTree(ccg) for ccg in ccg_xml_trees]))
  # For every token pair, extract linguistic relationships.
  relations_to_pairs = defaultdict(list)
  token_pairs = list(product(tokens, tokens))
  for i, (t1, t2) in enumerate(token_pairs):
    if t1 == t2:
      continue
    # Exclude symmetrical relationships.
    if (t2, t1) in token_pairs[:i]:
      continue
    relations = LinguisticRelationship(t1, t2)
    for relation in relations:
      relations_to_pairs[relation].append((t1, t2))
  # For every linguistic relationship, check if 'antonym' is present.
  # If it is present, then create an entry named:
  # Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x -> False.
  antonym_axioms = CreateAntonymAxioms(relations_to_pairs)
  # Return the axioms as a list.
  axioms = list(chain(*[antonym_axioms]))
  # axioms = list(chain(*[antonym_axioms, synonym_axioms, hypernym_axioms, hyponym_axioms]))
  return axioms
