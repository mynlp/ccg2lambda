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

# define the mapping from fine to coarse sem-tags
fine2coarse = dict()

#   anaphoric
fine2coarse['PRO'] = 'ANA'
fine2coarse['DEF'] = 'ANA'
fine2coarse['HAS'] = 'ANA'
fine2coarse['REF'] = 'ANA'
fine2coarse['EMP'] = 'ANA'

#   speech act
fine2coarse['GRE'] = 'ACT'
fine2coarse['ITJ'] = 'ACT'
fine2coarse['HES'] = 'ACT'
fine2coarse['QUE'] = 'ACT'

#   attribute
fine2coarse['QUC'] = 'ATT'
fine2coarse['QUV'] = 'ATT'
fine2coarse['COL'] = 'ATT'
fine2coarse['IST'] = 'ATT'
fine2coarse['SST'] = 'ATT'
fine2coarse['PRI'] = 'ATT'
fine2coarse['DEG'] = 'ATT'
fine2coarse['INT'] = 'ATT'
fine2coarse['REL'] = 'ATT'
fine2coarse['SCO'] = 'ATT'

#   comparative
fine2coarse['EQU'] = 'COM'
fine2coarse['MOR'] = 'COM'
fine2coarse['LES'] = 'COM'
fine2coarse['TOP'] = 'COM'
fine2coarse['BOT'] = 'COM'
fine2coarse['ORD'] = 'COM'

#   unnamed entity
fine2coarse['CON'] = 'UNE'
fine2coarse['ROL'] = 'UNE'
fine2coarse['GRP'] = 'UNE'

#   deixis
fine2coarse['DXP'] = 'DXS'
fine2coarse['DXT'] = 'DXS'
fine2coarse['DXD'] = 'DXS'

#   logical
fine2coarse['ALT'] = 'LOG'
fine2coarse['XCL'] = 'LOG'
fine2coarse['NIL'] = 'LOG'
fine2coarse['DIS'] = 'LOG'
fine2coarse['IMP'] = 'LOG'
fine2coarse['AND'] = 'LOG'

#   modality
fine2coarse['NOT'] = 'MOD'
fine2coarse['NEC'] = 'MOD'
fine2coarse['POS'] = 'MOD'

#   discourse
fine2coarse['SUB'] = 'DSC'
fine2coarse['COO'] = 'DSC'
fine2coarse['APP'] = 'DSC'
fine2coarse['BUT'] = 'DSC'

#   named entity
fine2coarse['PER'] = 'NAM'
fine2coarse['GPE'] = 'NAM'
fine2coarse['GPO'] = 'NAM'
fine2coarse['GEO'] = 'NAM'
fine2coarse['ORG'] = 'NAM'
fine2coarse['ART'] = 'NAM'
fine2coarse['HAP'] = 'NAM'
fine2coarse['UOM'] = 'NAM'
fine2coarse['CTC'] = 'NAM'
fine2coarse['URL'] = 'NAM'
fine2coarse['LIT'] = 'NAM'
fine2coarse['NTH'] = 'NAM'

#   events
fine2coarse['EXS'] = 'EVE'
fine2coarse['ENS'] = 'EVE'
fine2coarse['EPS'] = 'EVE'
fine2coarse['EXG'] = 'EVE'
fine2coarse['EXT'] = 'EVE'

#   tense and aspect
fine2coarse['NOW'] = 'TNS'
fine2coarse['PST'] = 'TNS'
fine2coarse['FUT'] = 'TNS'
fine2coarse['PRG'] = 'TNS'
fine2coarse['PFT'] = 'TNS'

#   temporal entity
fine2coarse['DAT'] = 'TIM'
fine2coarse['DOM'] = 'TIM'
fine2coarse['YOC'] = 'TIM'
fine2coarse['DOW'] = 'TIM'
fine2coarse['MOY'] = 'TIM'
fine2coarse['DEC'] = 'TIM'
fine2coarse['CLO'] = 'TIM'

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
        if stags[sent_index][word_index] in fine2coarse:
            token.set('costag', fine2coarse[stags[sent_index][word_index]])
        else:
            token.set('costag', 'UNK')
        word_index = word_index + 1

    word_index = 0
    for span in sent[1].findall('span'):
        surf = span.get('surf')
        if surf:
            span.set('stag', stags[sent_index][word_index])
            if stags[sent_index][word_index] in fine2coarse:
                span.set('costag', fine2coarse[stags[sent_index][word_index]])
            else:
                span.set('costag', 'UNK')
            word_index = word_index + 1

# write out result
tree.write(ofile)

