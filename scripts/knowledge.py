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
from linguistic_tools import get_wordnet_cascade
from normalization import denormalize_token, normalize_token

from subprocess import call, Popen
import subprocess
from nltk.corpus import wordnet as wn
import urllib.parse
import unicodedata


def get_tokens_from_xml_node(node):
    tokens = node.xpath(
        "//token[not(@base='*')]/@base | //token[@base='*']/@surf")
    return tokens


def get_lexical_relations(doc):
    # Get tokens from all CCG trees and de-normalize them.
    # (e.g. remove the preceding underscore).
    tokens = get_tokens_from_xml_node(doc)
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
    # Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x ->
    # False.
    antonym_axioms = create_antonym_axioms(relations_to_pairs)
    # Return the axioms as a list.
    axioms = list(itertools.chain(*[antonym_axioms]))
    return list(set(axioms))


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


def create_entail_axioms(relations_to_pairs, relation='synonym'):
    """
    For every linguistic relationship, check if 'relation' is present.
    If it is present, then create an entry named:
    Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x.
    """
    rel_pairs = relations_to_pairs[relation]
    axioms = []
    if not rel_pairs:
        return axioms
    for t1, t2 in rel_pairs:
        axiom = 'Axiom ax_{0}_{1}_{2} : forall x, _{1} x -> _{2} x.'\
                .format(relation, t1, t2)
        axioms.append(axiom)
    return axioms


def create_reventail_axioms(relations_to_pairs, relation='hyponym'):
    """
    For every linguistic relationship, check if 'relation' is present.
    If it is present, then create an entry named:
    Axiom ax_relation_token1_token2 : forall x, _token2 x -> _token1 x.
    Note how the predicates are reversed.
    """
    rel_pairs = relations_to_pairs[relation]
    axioms = []
    if not rel_pairs:
        return axioms
    for t1, t2 in rel_pairs:
        axiom = 'Axiom ax_{0}_{1}_{2} : forall x, _{2} x -> _{1} x.'\
                .format(relation, t1, t2)
        axioms.append(axiom)
    return axioms

def create_copy_axioms(relations_to_pairs, relation='copy'):
    """
    For every linguistic relationship, check if 'relation' is present.
    If it is present, then create an entry named:
    Axiom ax_relation_token1_token2 : forall x, _token1 x -> _token2 x.
    """
    rel_pairs = relations_to_pairs[relation]
    axioms = []
    if not rel_pairs:
        return axioms
    for t1, t2 in rel_pairs:
        axiom = 'Axiom ax_{0}_{1}_{2} : forall x, _{2} x.'\
                .format(relation, t1, t2)
        axioms.append(axiom)
    return axioms

def get_approx_relations_from_preds(premise_preds, conclusion_pred, threshold=0.3):
    #threshold is default=0.8, in paper=0.4, for similarity=0
    src_preds = [denormalize_token(p) for p in premise_preds]
    trg_pred = denormalize_token(conclusion_pred)
    approx_simil = []
    tmp_src_pred, trg_trg_pred = "", ""
    for src_pred in src_preds:
        if src_pred == trg_pred:
            continue
        if unicodedata.category(src_pred[0]) == "Lo":
            #if Japanese, do URL encode
            tmp_src_pred = urllib.parse.quote(src_pred)
            tmp_trg_pred = urllib.parse.quote(trg_pred)
        else:
            #for English
            tmp_src_pred = src_pred
            tmp_trg_pred = trg_pred
        process = Popen(\
            'curl http://localhost:5000/word2vec/similarity?w1='+ tmp_src_pred +'\&w2='+ tmp_trg_pred, \
            shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        similarity, err = process.communicate()
        try:
            approx_simil.append((float(similarity.decode()), src_pred))
        except ValueError:
            continue

    if len(approx_simil)==0:
        return []
    approx_simil_sorted = sorted(approx_simil, key=lambda x: x[0], reverse=True)
    if approx_simil_sorted[0][0] < threshold:
        return []
    best_pred = approx_simil_sorted[0][1]
    axioms = ['Axiom ax_{0}_{1}_{2} : forall x, _{1} x -> _{2} x.'\
        .format('approx', best_pred, trg_pred)]

    return axioms

def get_lexical_relations_from_preds(premise_preds, conclusion_pred, pred_args=None):
    src_preds = [denormalize_token(p) for p in premise_preds]
    trg_pred = denormalize_token(conclusion_pred)
    word_similarity = 0

    relations_to_pairs = defaultdict(list)
    relations_to_pairs_pre = []

    for src_pred in src_preds:
        before_src_pred, before_trg_pred = "", ""
        if src_pred == trg_pred or \
           src_pred in '_False' or \
           src_pred in '_True':
            continue
        if re.search("(.*?)\_[1-9]", src_pred):
            before_src_pred = src_pred
            src_pred = re.search("(.*?)\_[1-9]", src_pred).group(1)
        if re.search("(.*?)\_[1-9]", trg_pred):
            before_trg_pred = trg_pred
            trg_pred = re.search("(.*?)\_[1-9]", trg_pred).group(1)
        relations = linguistic_relationship(src_pred, trg_pred)
        # Choose only the highest-priority wordnet relation.
        relation = get_wordnet_cascade(relations)
        relations = [relation] if relation is not None else []
        for relation in relations:
            #  relations_to_pairs[relation].append((src_pred, trg_pred))
            word_similarity_list = []
            wordFromList1 = wn.synsets(src_pred)
            wordFromList2 = wn.synsets(trg_pred)
            for w1 in wordFromList1:
                for w2 in wordFromList2:
                    if w1.path_similarity(w2) is not None: 
                        word_similarity_list.append(w1.path_similarity(w2))
            if(word_similarity_list):
                word_similarity = max(word_similarity_list)
            if before_src_pred:
                src_pred = before_src_pred
            if before_trg_pred:
                trg_pred = before_trg_pred
            relations_to_pairs_pre.append([relation, src_pred, trg_pred, word_similarity])
        if before_src_pred:
            src_pred = before_src_pred
        if before_trg_pred:
            trg_pred = before_trg_pred
    # select the best predicate relation
    if len(relations_to_pairs_pre) > 0:
        best_relation, best_src_pred, best_trg_pred = relations_to_pairs_pre[0][0], relations_to_pairs_pre[0][1], relations_to_pairs_pre[0][2]
        for i, r in enumerate(relations_to_pairs_pre):
            if relations_to_pairs_pre[i][3] > relations_to_pairs_pre[i-1][3]:
                best_relation = relations_to_pairs_pre[i][0]
                best_src_pred = relations_to_pairs_pre[i][1]
                best_trg_pred = relations_to_pairs_pre[i][2]
            else:
                continue
        relations_to_pairs[relation].append((src_pred, trg_pred))

    # TODO: add pred_args into the axiom creation.
    antonym_axioms = create_antonym_axioms(relations_to_pairs)
    copy_axioms = create_copy_axioms(relations_to_pairs, 'copy')
    synonym_axioms = create_entail_axioms(relations_to_pairs, 'synonym')
    hypernym_axioms = create_entail_axioms(relations_to_pairs, 'hypernym')
    similar_axioms = create_entail_axioms(relations_to_pairs, 'similar')
    inflection_axioms = create_entail_axioms(relations_to_pairs, 'inflection')
    derivation_axioms = create_entail_axioms(relations_to_pairs, 'derivation')
    hyponym_axioms = create_reventail_axioms(relations_to_pairs)
    axioms = copy_axioms + antonym_axioms + synonym_axioms + hypernym_axioms + hyponym_axioms \
        + similar_axioms + inflection_axioms + derivation_axioms
    return list(set(axioms))
