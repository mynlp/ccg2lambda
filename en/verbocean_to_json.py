#!/usr/bin/python
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez
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

from __future__ import print_function
import argparse
from collections import defaultdict
import gzip
import json

parser = argparse.ArgumentParser()
parser.add_argument("infile")
parser.add_argument("outfile")
args = parser.parse_args()

def load_verbocean(verbocean_filename):
    relations = dict()
    with gzip.open(verbocean_filename, 'rt', 'utf-8') as fin:
        for line in fin:
            if not line.startswith('#'):
                verb1, rel, verb2 = line.split()[0:3]
                if verb1 not in relations:
                    relations[verb1] = defaultdict(set)
                relations[verb1][verb2].add(rel.strip('[]'))
    return relations

verbocean = load_verbocean(args.infile)
for v1, d in verbocean.items():
    for v2, rels in d.items():
        verbocean[v1][v2] = list(rels)
with open(args.outfile, 'w') as fout:
    json.dump(verbocean, fout, indent=2)
