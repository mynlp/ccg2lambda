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
import re

from linguistic_tools import linguistic_relationship
from normalization import denormalize_token

def get_tokens_from_ccg_tree(ccg_xml_tree):
    tokens = [denormalize_token(t) for t in ccg_xml_tree.xpath('//token/@base')]
    return tokens

def create_antonym_axioms(relations_to_pairs):
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

def get_lexical_relations(ccg_xml_trees):
    # Get tokens from all CCG trees and de-normalize them.
    # (e.g. remove the preceding underscore).
    tokens = list(itertools.chain(*[get_tokens_from_ccg_tree(ccg) for ccg in ccg_xml_trees]))
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
    return axioms
