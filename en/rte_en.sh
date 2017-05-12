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

# Script to Recognize Textual Entailment of problems in English.
# This script receives a file with several sentences (one per line), where all
# sentences are premises except the last one, which is a conclusion. It returns
# 'yes' (the premises entail the conclusion), 'no' (there is a contradiction) or
# 'unknown' (none of the former).
# You can use it as:
# 
# ./rte_en.sh <sentences.txt> <semantic_templates.yaml>
# 
# E.g.
# ./rte_en.sh en/sample_en.txt en/semantic_templates_en.yaml
#
# It should return 'yes'.
# You need to have a file in the en/ directory named candc_location.txt
# where you have the absolute directory path to C&C parser.
# Inside the directory pointed by candc_location.txt, there should be
# a directory called "bin" that contains the binaries of C&C parser
# and another directory called "models" that contains the models.
# For example:
# $ cat en/candc_location.txt
#   /home/pasmargo/software/candc/candc-1.00

USAGE="Usage: ./rte_en.sh <sentences.txt> <semantic_templates.yaml>"

# Check that the number of arguments is correct.
if [ "$#" -ne 2 ]; then
  echo "Error: Number of arguments invalid".
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

# This variable contains the name of the dataset (fracas or jsem).
sentences_fname=$1
sentences_basename=${sentences_fname##*/}
if [ ! -f $sentences_fname ]; then
  echo "Error: File with plain sentences does not exist."
  echo $USAGE
  exit 1
fi

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="plain" # tokenized sentences.
parsed_dir="parsed" # parsed sentences into XML or other formats.
results_dir="results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Tokenize text with Penn Treebank tokenizer.
cat $sentences_fname | \
  sed -f en/tokenizer.sed | \
  sed 's/ _ /_/g' \
  > ${plain_dir}/${sentences_basename}.tok

# Here we check whether the variable is pointing to the right C&C parser directory.
parser_dir=`cat en/candc_location.txt`
if [ ! -d "${parser_dir}" ]; then
  echo "Parser directory does not exist. Exit."
  exit 1
fi
if [ ! -e "${parser_dir}"/bin/candc ]; then
  echo "The variable parser_dir might not be pointing to the candc directory. Exit."
  exit 1
fi
# Set a variable with the command to invoke the CCG parser.
parser_cmd="${parser_dir}/bin/candc \
    --models ${parser_dir}/models \
    --candc-printer xml \
    --input"

# Syntactic parse the sentences into an XML file in $parsed_dir.
if [ ! -e "${parsed_dir}/${sentences_basename}.candc.xml" ]; then
  # C&C parse and conversion into transccg format.
  echo "Syntactic parsing ${plain_dir}/${sentences_basename}.tok"
  eval $parser_cmd ${plain_dir}/${sentences_basename}.tok \
    > ${parsed_dir}/${sentences_basename}.candc.xml \
    2> ${parsed_dir}/${sentences_basename}.log
fi
if [ ! -e "${parsed_dir}/${sentences_basename}.xml" ]; then
  python en/candc2transccg.py ${parsed_dir}/${sentences_basename}.candc.xml \
    > ${parsed_dir}/${sentences_basename}.xml
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
echo "Judging entailment for $parsed_dir/${sentences_basename}.sem.xml"
if [ ! -e "${results_dir}/${sentences_basename/.tok/.answer}" ]; then
  python scripts/prove.py \
    $parsed_dir/${sentences_basename}.sem.xml \
    --graph_out ${results_dir}/${sentences_basename}.html \
    --abduction \
    > ${results_dir}/${sentences_basename}.answer \
    2> ${results_dir}/${sentences_basename}.err
fi
echo "Judgement: "`cat ${results_dir}/${sentences_basename}.answer`
