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

import json
from nltk.corpus import wordnet as wn

# Obtain lemmas of synonyms.
def obtain_synonyms(word):
    return set([lemma for synonym in wn.synsets(word) \
                       for lemma in synonym.lemma_names()])

# Obtain lemmas of hypernyms.
def obtain_hypernyms(word):
    hyper = lambda s: s.hypernyms()
    return set([lemma for synonym in wn.synsets(word) \
                        for hypernym in synonym.closure(hyper) \
                          for lemma in hypernym.lemma_names()])

# Obtain lemmas of hyponyms.
def obtain_hyponyms(word):
    return set([lemma for synonym in wn.synsets(word) \
                        for hyponym in synonym.hyponyms() \
                          for lemma in hyponym.lemma_names()])

# Obtain lemmas of holonyms.
def obtain_holonyms(word):
    return set([lemma for synonym in wn.synsets(word) \
                        for holonym in synonym.member_holonyms() + \
                                       synonym.substance_holonyms() + \
                                       synonym.part_holonyms() \
                          for lemma in holonym.lemma_names()])

# Obtain lemmas of meronyms.
def obtain_meronyms(word):
    return set([lemma for synonym in wn.synsets(word) \
                        for meronym in synonym.member_meronyms() + \
                                       synonym.substance_meronyms() + \
                                       synonym.part_meronyms() \
                          for lemma in meronym.lemma_names()])

# Obtain lemmas of antonyms.
def obtain_antonyms(word):
    return set([antonym.name() for synonym in wn.synsets(word) \
                               for lemma in synonym.lemmas() \
                                 for antonym in lemma.antonyms()])

# Obtain lemmas of entailments.
def obtain_entailments(word):
    return set([lemma for synonym in wn.synsets(word) \
                        for entailment in synonym.entailments()\
                          for lemma in entailment.lemma_names()])

# Obtain derivationally related words.
def obtain_derivations(word):
    return set([drf.name() for synonym in wn.synsets(word) \
                           for lemma in synonym.lemmas() \
                             for drf in lemma.derivationally_related_forms()])

# Returns the linguistic relationships of a word. E.g.
# obtain_linguistic_relationships('friend') should return:
# [('antonym', 'foe'), ('synonym', 'mate'), ('hypernym', 'person'), etc.]
def obtain_linguistic_relationships(word):
    word = word.strip('"')
    linguistic_relationships = []
    linguistic_relationships.append(('copy', word))
    base_word = wn.morphy(word)
    if base_word == None:
        base_word = word.lower()
    if word != base_word:
        linguistic_relationships.append(('inflection', base_word))
    linguistic_relationships.extend(\
      [('synonym', lemma) for lemma in obtain_synonyms(word)])
    linguistic_relationships.extend(\
      [('hypernym', lemma) for lemma in obtain_hypernyms(word)])
    linguistic_relationships.extend(\
      [('hyponym', lemma) for lemma in obtain_hyponyms(word)])
    linguistic_relationships.extend(\
      [('holonym', lemma) for lemma in obtain_holonyms(word)])
    linguistic_relationships.extend(\
      [('meronym', lemma) for lemma in obtain_meronyms(word)])
    linguistic_relationships.extend(\
      [('antonym', lemma) for lemma in obtain_antonyms(word)])
    linguistic_relationships.extend(\
      [('entailed', lemma) for lemma in obtain_entailments(word)])
    linguistic_relationships.extend(\
      [('derivation', lemma) for lemma in obtain_derivations(word)])
    return linguistic_relationships

# Check if word1 is synonym of word2, but checking whether the intersection
# between the synset of word1 and the synset of word2.
# If word1 = 'car' and word2 = 'automobile', this function should return True.
def is_synonym(word1, word2):
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    common_synset = set(synsets_word1).intersection(set(synsets_word2))
    if len(common_synset) != 0:
        return True
    return False

# Check whether word1 is a hypernym of word2, by computing the synset of word2,
# and for every possible meaning of word2, compute whether the hypernym of
# such meaning is in the list of synonyms (synset) of word1. E.g.
# is_hypernym('European', 'Swede') returns True.
def is_hypernym(word1, word2):
    hyper = lambda s: s.hypernyms()
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    for synonym in synsets_word2:
        for hypernym in synonym.closure(hyper):
            if hypernym in synsets_word1:
                return True
    return False

# Adjective similarity. E.g. big <-> huge.
def is_similar(word1, word2):
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    similar_word1 = set(similar for s in synsets_word1 for similar in s.similar_tos())
    return True if len(similar_word1.intersection(synsets_word2)) > 0 else False

# Check whether word1 is a hyponym of word2, by computing whether
# word2 is a hypernym of word1. E.g.
# is_hyponym('Swede', 'European') returns True.
def is_hyponym(word1, word2):
    return is_hypernym(word2, word1)

# Check whether word1 is a holonym of word2, by computing the synset of word2,
# for every meaning of word2 compute its holonym, and check if such holonym
# is in the list of meanings (synset) of word1. E.g.
# is_holonym('door', 'lock') returns True.
def is_holonym(word1, word2):
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    for synonym in synsets_word2:
        holonyms = synonym.member_holonyms() + \
                   synonym.substance_holonyms() + \
                   synonym.part_holonyms()
        for holonym in holonyms:
            if holonym in synsets_word1:
                return True
    return False

# Check whether word1 is a meronym of word2, by computing whether
# word2 is a holonym of word1. E.g.
# is_meronym('lock', 'door') returns True.
def is_meronym(word1, word2):
    return is_holonym(word2, word1)

# Checks whether word1 is an antonym of word2.
# Note that it may also consider antonyms words with different POS tags. E.g.
# is_antonym('fast', 'slowly') returns True <- fast is adjective, slowly is adverb.
# is_antonym('fast', 'slow') returns True.
# is_antonym('good', 'bad') returns True.
# is_antonym('good', 'poor') returns False.
def is_antonym(word1, word2):
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    antonyms = []
    for synonym in synsets_word1:
        for lemma in synonym.lemmas():
            antonyms.extend(lemma.antonyms()) # antonyms() method only works on lemmas.
    antonym_names = [antonym.name() for antonym in antonyms]
    for antonym_name in antonym_names:
        synsets_antonym = wn.synsets(antonym_name)
        common_meanings = set(synsets_word2).intersection(set(synsets_antonym))
        if len(common_meanings) > 0:
            return True
    return False

# Checks whether word1 is entailed by word2. E.g.
# is_entailed('chew', 'eat') returns True. Only works on verbs.
def is_entailed(word1, word2):
    synsets_word1 = wn.synsets(word1)
    synsets_word2 = wn.synsets(word2)
    for synonym in synsets_word2:
        entailments = synonym.entailments()
        if len(set(entailments).intersection(set(synsets_word1))):
            return True
    return False

# Snippet found in Stackoverflow.
def nounify(verb_word):
    """ Transform a verb to the closest noun: die -> death """
    verb_synsets = wn.synsets(verb_word, pos="v")
    # Word not found
    if not verb_synsets:
        return []
    # Get all verb lemmas of the word
    verb_lemmas = [l for s in verb_synsets \
                       for l in s.lemmas() if s.name().split('.')[1] == 'v']
    # Get related forms
    derivationally_related_forms = \
      [(l, l.derivationally_related_forms()) for l in verb_lemmas]
    # filter only the nouns
    related_noun_lemmas = [l for drf in derivationally_related_forms \
                           for l in drf[1] if l.synset.name().split('.')[1] == 'n']
    # Extract the words from the lemmas
    words = [l.name() for l in related_noun_lemmas]
    len_words = len(words)
    # Build the result in the form of a list containing tuples (word, probability)
    result = [(w, float(words.count(w))/len_words) for w in set(words)]
    result.sort(key=lambda w: -w[1])
    # return all the possibilities sorted by probability
    return result

# Check if word1 and word2 are inflectionally or derivationally related words,
# that is, words that had variations in their morphemes or that changed
# their POS category (e.g. converted from verb to noun).
def is_derivation(word1, word2):
    synsets_word1 = wn.synsets(word1)
    # Word not found
    if not synsets_word1:
        return False
    # Get all lemmas of word1
    lemmas = [l for s in synsets_word1 for l in s.lemmas()]
    # Get related forms
    derivationally_related_forms = \
      [drf for l in lemmas for drf in l.derivationally_related_forms()]
    # Get a list of tuples, of the form [(lemma_name, POS), ...]
    lemma_pos = \
      [(l.name(), l.synset().name().split('.')[1]) for l in derivationally_related_forms]
    # Returns True if word2 is in the list of lemma names
    # that are derivations of word1.
    return (word2 in [l[0] for l in lemma_pos])

# Load VerbOcean dictionary.
try:
    with open('en/verbocean.json', 'r') as fin:
        verbocean = json.load(fin)
except:
    verbocean = {}

# Query the verbocean dictionary and return a (possibly empty)
# set of relations between two verbs.
def get_verbocean_relations(verb1, verb2):
    if verb1 in verbocean and verb2 in verbocean[verb1]:
        return set(verbocean[verb1][verb2])
    return set()

# Find linguistic relationship between two words.
# Remaining relationships that I would like to implement:
# linguistic_relationship('man', 'men') would return 'plural'.
# linguistic_relationship('go', 'went') would return 'present'.
# BUG: linguistic_relationship('man', 'men') returns
#   ['synonym', 'hypernym', 'hyponym'] because 'man' and 'men' have the same
#   lemma but wn.morphy cannot recognize it. We should detect this and prevent
#   those relationships from triggering. However,
#   linguistic_relationship('woman', 'women') returns ['inflection'] as expected,
#   until we implement the 'plural' relationship.
def linguistic_relationship(word1, word2):
    (word1, word2) = (word1.strip('"'), word2.strip('"'))
    if word1 == word2:
        return ['copy']
    base_word1 = wn.morphy(word1)
    base_word2 = wn.morphy(word2)
    if base_word1 == None:
        base_word1 = word1.lower()
    if base_word2 == None:
        base_word2 = word2.lower()
    ling_relations = []
    if word1 != word2 and base_word1 == base_word2:
        return ['inflection']
    if is_synonym(base_word1, base_word2):
        ling_relations.append('synonym')
    if is_hypernym(base_word1, base_word2):
        ling_relations.append('hyponym')
    if is_hyponym(base_word1, base_word2):
        ling_relations.append('hypernym')
    if is_similar(base_word1, base_word2):
        ling_relations.append('similar')
    if is_holonym(base_word1, base_word2):
        ling_relations.append('holonym')
    if is_meronym(base_word1, base_word2):
        ling_relations.append('meronym')
    if is_antonym(base_word1, base_word2):
        ling_relations.append('antonym')
    if is_entailed(base_word1, base_word2):
        ling_relations.append('entailed')
    if is_derivation(word1, word2):
        ling_relations.append('derivation')
    # Typical types of verbocean relations are "happens-before" or "stronger-than"
    ling_relations.extend(get_verbocean_relations(base_word1, base_word2))
    return ling_relations

def get_wordnet_cascade(ling_relations):
  """
  Receives a list of linguistic relations (strings),
  and returns one of those linguistic relations with highest priority:
  copy > inflection > derivation > synonym > antonym >
  hypernym > hyponym > sister > cousin > None.
  """
  relation = None
  if 'copy' in ling_relations:
    relation = 'copy'
  elif 'inflection' in ling_relations:
    relation = 'inflection'
  elif 'derivation' in ling_relations:
    relation = 'derivation'
  elif 'synonym' in ling_relations:
    relation = 'synonym'
  elif 'antonym' in ling_relations:
    relation = 'antonym'
  elif 'hypernym' in ling_relations:
    relation = 'hypernym'
  elif 'similar' in ling_relations:
    relation = 'similar'
  elif 'hyponym' in ling_relations:
    relation = 'hyponym'
  elif any(lr.startswith('sister') for lr in ling_relations):
    sister_rels = [lr for lr in ling_relations if lr.startswith('sister')]
    assert sister_rels
    relation = sister_rels[0]
  elif any(lr.startswith('cousin') for lr in ling_relations):
    cousin_rels = [lr for lr in ling_relations if lr.startswith('cousin')]
    assert cousin_rels
    relation = cousin_rels[0]
  return relation
