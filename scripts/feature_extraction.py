#!/usr/bin/python

import os
import glob
import requests
import numpy as np

from collections import defaultdict
from scipy.spatial.distance import cosine
from scipy.spatial.distance import euclidean
from scipy.spatial.distance import jaccard
from nltk.corpus import wordnet as wn
from nltk.corpus.reader.wordnet import WordNetError
from gensim import corpora, models, similarities, matutils
import config
import math
from lxml import etree
import re

def get_overlap(sentence_a, sentence_b):
    sentence1_set = set(sentence_a)
    sentence2_set = set(sentence_b)
    return len(sentence1_set & sentence2_set)/ float(len(sentence1_set | sentence2_set))

def sentence_lengths(sentence_a, sentence_b):
    return float((len(sentence_a)+len(sentence_b))/2)

def word_overlap2(sentence_a, sentence_b):
    a_set = set(word for word in sentence_a) - config.stop_list
    b_set = set(word for word in sentence_b) - config.stop_list
    score = len(a_set&b_set)/float(len(a_set|b_set))# len(s1&s2)/max(len(s1),len(s2))
    score = (len(a_set|b_set)-len(b_set))/len(a_set) #8337

    return score

def sentence_lengths_difference(sentence_a, sentence_b):
    return abs(len(sentence_a)-len(sentence_b))/float(min(len(sentence_a),len(sentence_b)))
          
def get_synset_overlap(sentence_a, sentence_b):
    def synsets(word):
        sense_lemmas = []
        for pos in ('n'):#,'a'):
            for i in range(10):
                try:
                    sense_lemmas += [lemma.name for lemma in wn.synset('{0}.{1}.0{2}'.format(word, pos, i)).lemmas()]
                except WordNetError: 
                    pass
        return sense_lemmas

    a_set = set(lemma for word in sentence_a for lemma in synsets(word))
    b_set = set(lemma for word in sentence_b for lemma in synsets(word))
    score = len(a_set&b_set)/float(len(a_set|b_set))
    
    return score

def synset_overlap(sentence_a, sentence_b):
    score = get_synset_overlap(sentence_a, sentence_b)
    return score

def get_synset_distance(sentence_a, sentence_b):
    def distance(word, sentence_b):
        try:
            synset_a = wn.synset('{0}.n.01'.format(word))
        except WordNetError:
            return 0.0

        max_similarity = 0.0
        for word2 in sentence_b:
            try:
                similarity = synset_a.path_similarity(wn.synset('{0}.n.01'.format(word2)))
                if similarity > max_similarity:
                    max_similarity = similarity
            except WordNetError:
                continue

        return max_similarity

    distances = [distance(word, sentence_b) for word in sentence_a]
    if float(len([1 for i in distances if i > 0.0])) == 0:
        return 0
    return sum(distances)/float(len([1 for i in distances if i > 0.0]))

def synset_distance(sentence_a, sentence_b):
    score = get_synset_distance(sentence_a, sentence_b)            
    return score

def pred_overlap(sick_id):
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        pred1 = set(tree.xpath("//span[contains(@id, 's0')]/@type"))
        pred2 = set(tree.xpath("//span[contains(@id, 's1')]/@type"))

        return len(pred1&pred2)/float(len(pred1|pred2))

def type_overlap(sick_id):
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        type1, type2 = [], []
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        pred1 = tree.xpath("//span[contains(@id, 's0')]/@type")
        for p1 in pred1:
            types = p1.split(":")
            type1.append(types[1].strip())
        pred2 = tree.xpath("//span[contains(@id, 's1')]/@type")
        for p2 in pred2:
            types = p2.split(":")
            type2.append(types[1].strip())

        return len(set(type1)&set(type2))/float(len(set(type1)|set(type2)))
    
def pos_overlap(sick_id):
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        pos1 = set(tree.xpath("//token[contains(@id, 't0')]/@pos"))
        pos2 = set(tree.xpath("//token[contains(@id, 't1')]/@pos"))
        return len(pos1&pos2)/float(len(pos1|pos2))

def get_nouns(root):
    nouns = []
    for child in root:
        noun = False
        if child.get("pos") == 'NN' or child.get("pos") == 'NNS':
            noun = True
        if noun == True:
            nounword = child.get("base")
            nouns.append(nounword)
    return nouns

def noun_overlap(sick_id):
    score = 0
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        t_set = set(get_nouns(tree.xpath("//token[contains(@id, 't0')]")))
        h_set = set(get_nouns(tree.xpath("//token[contains(@id, 't1')]")))
    if float(len(t_set | h_set)) > 0:
        score = len(t_set & h_set) / float(len(t_set | h_set))
    return score
    
def get_verbs(root):
    verbs = []
    for child in root:
        verb = False
        if child.get("pos") == 'VBP' or child.get("pos") == 'VBG':
            verb = True
        if verb == True:
            verbword = child.get("base")
            verbs.append(verbword)
    return verbs

def verb_overlap(sick_id):
    score = 0
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        t_set = set(get_verbs(tree.xpath("//token[contains(@id, 't0')]")))
        h_set = set(get_verbs(tree.xpath("//token[contains(@id, 't1')]")))
    if float(len(t_set | h_set)) > 0:
        score = len(t_set & h_set) / float(len(t_set | h_set))
    return score

def tfidf(sick_id):
    corpus = config.bow_corpus
    num = config.ids[sick_id]
    score = matutils.cossim(config.tfidf_model[corpus[2*num-2]], config.tfidf_model[corpus[2*num-1]])
    return score

def lsi(sick_id):
    corpus = config.bow_corpus
    tfidf = config.tfidf_model[corpus]
    num = config.ids[sick_id]
    score = matutils.cossim(config.lsi_model[tfidf[2*num-2]], config.lsi_model[tfidf[2*num-1]])
    return score

def lda(sick_id):
    corpus = config.bow_corpus
    num = config.ids[sick_id]
    score = matutils.cossim(config.lda_model[corpus[2*num-2]], config.lda_model[corpus[2*num-1]])
    return score

def tfidf_msr(sick_id, kind):
    corpus = config.bow_corpus_msr
    if kind == "train":
        num = int(sick_id)
    else:
        num = int(sick_id) * 2
    score = matutils.cossim(config.tfidf_model_msr[corpus[2*num-2]], config.tfidf_model_msr[corpus[2*num-1]])
    return score

def lsi_msr(sick_id, kind):
    corpus = config.bow_corpus_msr
    tfidf = config.tfidf_model_msr[corpus]
    if kind == "train":
        num = int(sick_id)
    else:
        num = int(sick_id) * 2
    score = matutils.cossim(config.lsi_model_msr[tfidf[2*num-2]], config.lsi_model_msr[tfidf[2*num-1]])
    return score

def lda_msr(sick_id, kind):
    corpus = config.bow_corpus_msr
    if kind == "train":
        num = int(sick_id)
    else:
        num = int(sick_id) * 2
    score = matutils.cossim(config.lda_model_msr[corpus[2*num-2]], config.lda_model_msr[corpus[2*num-1]])
    return score

def get_passive(root):
    passives = 0
    for child in root:
        if re.search("pss=true", child.get("cat")):
            passives += 1
    return passives

def passive_overlap(sick_id):
    score = 0
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        t_set = get_passive(tree.xpath("//token[contains(@id, 't0')]"))
        h_set = get_passive(tree.xpath("//token[contains(@id, 't1')]"))
    if t_set == h_set:
        return 0
    else:
        return 1    

def get_negation(root):
    negations = 0
    for child in root:
        if re.search("-exists", child):
            negations += 1
    return negations

def negation_overlap(sick_id):
    score = 0
    if glob.glob("./parsed/*_"+sick_id+".sem.xml") is None:
        return 0
    else:
        file = glob.glob("./parsed/*_"+sick_id+".sem.xml")
        parser = etree.XMLParser(remove_blank_text=True)
        tree = etree.parse(file[0], parser)
        t_set = get_negation(tree.xpath("//semantics[contains(@root, 's0_sp0')]//@sem"))
        h_set = get_negation(tree.xpath("//semantics[contains(@root, 's1_sp0')]//@sem"))
    if t_set == h_set:
        return 0
    else:
        return 1  
