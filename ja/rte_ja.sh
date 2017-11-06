#!/bin/bash
#
#  Copyright 2016 Pascual Martinez-Gomez
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

# Script to Recognize Textual Entailment of problems in Japanese.
# This script receives a file with several sentences (one per line), where all
# sentences are premises except the last one, which is a conclusion. It returns
# 'yes' (the premises entail the conclusion), 'no' (there is a contradiction) or
# 'unknown' (none of the former).
# You can use it as:
# 
# ./rte_ja.sh <sentences.txt> <semantic_templates.yaml>
# 
# E.g.
# ./rte_ja.sh sample_en.txt semantic_templates_ja.yaml
#
# It should return 'yes'.
# You need to have a file in the current directory named jigg_location.txt
# where you have the absolute directory path to Jigg parser.
# Inside the directory pointed by candc_location.txt, there should be
# a directory called "bin" that contains the binaries of C&C parser
# and another directory called "models" that contains the models.
# For example:
# $ cat jigg_location.txt
#   /home/pasmargo/software/jigg

USAGE="Usage: ./ja/rte_ja.sh <sentences.txt> <semantic_templates.yaml>"

# Check that the number of arguments is correct.
if [ "$#" -ne 2 ]; then
  echo "Error: Number of arguments invalid".
  echo $USAGE
  exit 1
fi

# This variable contains the filename of the RTE problem.
sentences_fname=$1
sentences_basename=${sentences_fname##*/}
if [ ! -f $sentences_fname ]; then
  echo "Error: File with plain sentences does not exist."
  echo $USAGE
  exit 1
fi

# This variable contains the filename where the category templates are.
category_templates=$2
if [ ! -f $category_templates ]; then
  echo "Error: File with semantic templates does not exist."
  echo $USAGE
  exit 1
fi

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="ja_plain" # tokenized sentences.
parsed_dir="ja_parsed" # parsed sentences into XML or other formats.
results_dir="ja_results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Here we check whether the variable is pointing to the right C&C parser directory.
parser_dir=`cat ja/jigg_location.txt`
if [ ! -d "${parser_dir}/jar" ]; then
  echo "Parser directory does not exist. Exit."
  exit 1
fi
if [ ! -e "${parser_dir}"/jar/ccg-models-*.jar ]; then
  echo "Japanese CCG models not found. Refer to Jigg instructions to download them."
  exit 1
fi
# Set a variable with the command to invoke the CCG parser for Japanese.
parser_cmd="java -Xmx4g -cp \"${parser_dir}/jar/*\" jigg.pipeline.Pipeline \
  -annotators ssplit,kuromoji,ccg \
  -ccg.kBest 10 -file"

# Syntactic parse the sentences into an XML file in $parsed_dir.
if [ ! -e "${parsed_dir}/${sentences_basename}.jigg.xml" ]; then
  # C&C parse and conversion into transccg format.
  echo "Syntactic parsing ${sentences_fname}"
  # This will create a file ${sentences_fname}.xml
  eval $parser_cmd ${sentences_fname} \
    > ${parsed_dir}/${sentences_basename}.log.std \
    2> ${parsed_dir}/${sentences_basename}.log.err
  mv ${sentences_fname}.xml ${parsed_dir}/${sentences_basename}.jigg.xml
fi

if [ ! -e "${parsed_dir}/${sentences_basename}.xml" ]; then
  cp ${parsed_dir}/${sentences_basename}.jigg.xml ${parsed_dir}/${sentences_basename}.xml
fi

# Semantic parsing the CCG trees in XML.
if [ ! -e "$parsed_dir/${sentences_basename}.sem.xml" ]; then
  echo "Semantic parsing $parsed_dir/${sentences_basename}.xml"
  python scripts/semparse.py \
    $parsed_dir/${sentences_basename}.xml \
    $category_templates \
    $parsed_dir/${sentences_basename}.sem.xml \
    --arbi-types \
    2> $parsed_dir/${sentences_basename}.sem.err
fi

# Judge entailment with a theorem prover (Coq, at the moment).
if [ ! -e "${results_dir}/${sentences_basename}.answer" ]; then
  start_time=`python -c 'import time; print(time.time())'`
  python scripts/prove.py \
    $parsed_dir/${sentences_basename}.sem.xml \
    --graph_out ${results_dir}/${sentences_basename}.html \
    > ${results_dir}/${sentences_basename}.answer \
    2> ${results_dir}/${sentences_basename}.err
  end_time=`python -c 'import time; print(time.time())'`
  echo "${end_time} - ${start_time}" | \
    bc -l | awk '{printf("%.2f\n", $1)}' \
    > ${results_dir}/${sentences_basename}.time
fi
echo "Judged entailment for $parsed_dir/${sentences_basename}.sem.xml "`cat ${results_dir}/${sentences_basename}.answer`
