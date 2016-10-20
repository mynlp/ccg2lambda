#!/bin/bash

# This is a script to do evaluation for NLP2016.
#
# ./nlp2016exp.sh <cores> <result_dir>
#

cores=${1:-3}
results_dir=$2

cp coqlib_ja.v coqlib.v
coqc coqlib.v

### Plain results ###
./nlp2016exp_set.sh $cores $results_dir plain
./nlp2016exp_eval.sh $results_dir plain

### Gold-tree results ###
# Remove semantically-parsed files from previous plain run.
rm ja_parsed/*.sem.*
# Copying gold parse trees onto the ja_parse directory
cp ja_parsed_gold/*.xml ja_parsed/
./nlp2016exp_set.sh $cores $results_dir gold
./nlp2016exp_eval.sh $results_dir gold

