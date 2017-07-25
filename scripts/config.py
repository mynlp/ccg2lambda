#!/usr/bin/python
from gensim import corpora, models, similarities, matutils
import os

stop_list = set(['a', 'of', 'is', 'the']) 

bow_corpus = corpora.MmCorpus('./tmp/bowvector.mm') #bag-of-words vector corpus
tfidf_model = models.TfidfModel.load('./tmp/tfidf.mm') 				#TF-IDF vector model
lsi_model = models.LsiModel.load('./tmp/lsi.mm') 					#LSI vector model
lda_model = models.LdaModel.load('./tmp/lda.mm')					#LDA vector model
f = open("./tmp/sick_ids.txt", "r")
id_lists = f.readlines()
f.close()
ids = {}
for id_list in id_lists:
	num = id_list.split(",")[0]
	sick_id = id_list.split(",")[1].strip()
	ids[str(sick_id)] = int(num)

bow_corpus_msr = corpora.MmCorpus('./tmp/bowvector_2012.mm') #bag-of-words vector corpus
tfidf_model_msr = models.TfidfModel.load('./tmp/tfidf_2012.mm')              #TF-IDF vector model
lsi_model_msr = models.LsiModel.load('./tmp/lsi_2012.mm')                    #LSI vector model
lda_model_msr = models.LdaModel.load('./tmp/lda_2012.mm')                    #LDA vector model



