# -*- coding: utf-8 -*-
#
#  Copyright 2018 Joan Gines i Ametlle
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

import sys
import codecs
import string
from lxml import etree

# source xml file to inject tokens to
ifile = sys.argv[1]

# source file with tagged sentences
semfile = sys.argv[2]

# output file
ofile = sys.argv[3]

# extract semantic tags
stags = [[]]
sent_index = 0

for line in codecs.open(semfile, mode = 'r', errors = 'ignore', encoding = 'utf-8'):
    line = line[:-1]
    if line:
        tag, _ = line.split('\t')
        stags[sent_index].append(tag)
    else:
        stags.append([])
        sent_index = sent_index + 1

# navigate the tags contained in the xml tree
tree = etree.parse(ifile)
root = tree.getroot()
sent_index = -1
word_index = -1

for sent in root.iter('sentence'):
    sent_index = sent_index + 1

    word_index = 0
    for token in sent[0].findall('token'):
        token.set('stag', stags[sent_index][word_index])
        word_index = word_index + 1

    word_index = 0
    for span in sent[1].findall('span'):
        surf = span.get('surf')
        if surf:
            span.set('stag', stags[sent_index][word_index])
            word_index = word_index + 1

# write out result
tree.write(ofile)

