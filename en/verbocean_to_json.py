#!/usr/bin/python
# -*- coding: utf-8 -*-
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
