#!/usr/bin/python
#
#  Copyright 2017 Hitomi Yanaka
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
from gensim import corpora, models, similarities, matutils
import os

stop_list = set(['a', 'of', 'is', 'the']) 

bow_corpus = corpora.MmCorpus('./en/models/bowvector.mm') #bag-of-words vector corpus
tfidf_model = models.TfidfModel.load('./en/models/tfidf.mm') 				#TF-IDF vector model
lsi_model = models.LsiModel.load('./en/models/lsi.mm') 					#LSI vector model
lda_model = models.LdaModel.load('./en/models/lda.mm')					#LDA vector model
f = open("./en/models/sick_ids.txt", "r")
id_lists = f.readlines()
f.close()
ids = {}
for id_list in id_lists:
	num = id_list.split(",")[0]
	sick_id = id_list.split(",")[1].strip()
	ids[str(sick_id)] = int(num)

bow_corpus_msr = corpora.MmCorpus('./en/models/bowvector_2012.mm') #bag-of-words vector corpus
tfidf_model_msr = models.TfidfModel.load('./en/models/tfidf_2012.mm')              #TF-IDF vector model
lsi_model_msr = models.LsiModel.load('./en/models/lsi_2012.mm')                    #LSI vector model
lda_model_msr = models.LdaModel.load('./en/models/lda_2012.mm')                    #LDA vector model



