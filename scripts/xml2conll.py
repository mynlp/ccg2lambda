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
import string
from lxml import etree

# source xml file to extract tokens from
ifile = sys.argv[1]

# navigate the tags contained in the xml tree
tree = etree.parse(ifile)
root = tree.getroot()
num_sents = 0

for sent in root.iter('sentence'):
    if num_sents > 0:
        print('')
    for token in sent[0].findall('token'):
        print(token.get('surf'))
    num_sents = num_sents + 1

