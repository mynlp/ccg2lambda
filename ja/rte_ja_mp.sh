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

# Script to Recognize Textual Entailment of problems in Japanese, using
# multiple CCG parsers (Jigg and depccg at the moment).
# This script receives a file with several sentences (one per line), where all
# sentences are premises except the last one, which is a conclusion. It returns
# 'yes' (the premises entail the conclusion), 'no' (there is a contradiction) or
# 'unknown' (none of the former).
# You can use it as:
#
# ./rte_ja_mp.sh <sentences.txt> <semantic_templates.yaml> <nbest>
#
# E.g.
# ./rte_ja_mp.sh ja/sample_ja.txt ja/semantic_templates_ja.yaml 3

USAGE="Usage: ./rte_ja_mp.sh <sentences.txt> <semantic_templates.yaml> <nbest>"

# Set the number of nbest parses (Default: 1)
nbest=${3:-1}

# Create a file named "parser_location_ja.txt" at the "ja" directory and
# write a list of CCG parsers installed, as in:
# $ cat ja/parser_location_ja.txt
# jigg:/path/to/ccg2lambda/ja/jigg-v-0.4
# depccg:/path/to/depccg/build

# Check that the number of arguments is correct.
# if [ "$#" -ne 2 ]; then
#   echo "Error: Number of arguments invalid".
#   echo $USAGE
#   exit 1
# fi

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
plain_dir="ja_plain" # tokenized sentences.
parsed_dir="ja_parsed" # parsed sentences into XML or other formats.
results_dir="ja_results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Copy the input text to plain_dir
if [ ! -f ${plain_dir}/${sentences_basename} ]; then
  cp $sentences_fname ${plain_dir}/${sentences_basename}
fi

function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }

# Set parser locations
if [ ! -f "ja/parser_location_ja.txt" ]; then
  echo "Error: File ja/parser_location_ja.txt does not exist."
  exit 1
fi
for parser in `cat ja/parser_location_ja.txt`; do
  parser_name=`echo $parser | awk -F':' '{print $1}'`
  parser_dir=`echo $parser | awk -F':' '{print $2}'`
  if [ "${parser_name}" == "jigg" ]; then
    jigg_dir=${parser_dir}
    if [ ! -d "${jigg_dir}/jar" ]; then
      echo "Parser directory does not exist. Exit."
      exit 1
    fi
    if [ ! -e "${parser_dir}"/jar/ccg-models-*.jar ]; then
      echo "Japanese CCG models not found. Refer to Jigg instructions to download them."
      exit 1
    fi
  fi
  if [ "${parser_name}" == "depccg" ]; then
    depccg_dir=${parser_dir}
    if [ ! -d "${depccg_dir}" ] || [ ! -e "${depccg_dir}"/src/run.py ]; then
      echo "depccg parser directory incorrect. Exit."
      exit 1
    fi
  fi
done

# Set a variable with the command to invoke Jigg
parser_cmd="java -Xmx4g -cp \"${jigg_dir}/jar/*\" jigg.pipeline.Pipeline \
  -annotators ssplit,kuromoji,ccg \
  -ccg.kBest \"${nbest}\" -file"

tagging_cmd="java -Xmx4g -cp \"${jigg_dir}/jar/*\" jigg.pipeline.Pipeline \
  -annotators ssplit,kuromoji -file"

function parse_jigg() {
  # Parse using jigg.
  base_fname=$1
  eval $parser_cmd ${plain_dir}/$base_fname \
    > ${parsed_dir}/${base_fname}.log.std \
    2> ${parsed_dir}/${base_fname}.log.err
  mv ${plain_dir}/${base_fname}.xml ${parsed_dir}/${base_fname}.jigg.jigg.xml
}

function parse_depccg() {
  # Parse using depccg.
  base_fname=$1
  eval $tagging_cmd ${plain_dir}/$base_fname \
    > ${parsed_dir}/${base_fname}.log.std \
    2> ${parsed_dir}/${base_fname}.log.err
  mv ${plain_dir}/${base_fname}.xml ${parsed_dir}/${base_fname}.tagged.xml
  env PYTHONPATH=$depccg_dir/src:$PYTHONPATH \
    python ja/rte.py \
    ${depccg_dir}/models/ja_headfinal \
    ja \
    ${parsed_dir}/${base_fname}.tagged.xml \
    --nbest "${nbest}" \
    > ${parsed_dir}/${base_fname}.depccg.jigg.xml
}

function semantic_parsing() {
  parser=$1
  sentences_basename=$2
  python scripts/semparse.py \
    $parsed_dir/${sentences_basename}.${parser}.jigg.xml \
    $category_templates \
    $parsed_dir/${sentences_basename}.${parser}.sem.xml \
    --arbi-types \
    2> $parsed_dir/${sentences_basename}.${parser}.sem.err
}

function proving() {
  parser=$1
  sentences_basename=$2
  start_time=`python -c 'import time; print(time.time())'`
    timeout 100 python scripts/prove.py \
      ${parsed_dir}/${sentences_basename}.${parser}.sem.xml \
      --graph_out ${results_dir}/${sentences_basename}.${parser}.html \
      --proof ${results_dir}/${sentences_basename}.${parser}.coq.xml \
      > ${results_dir}/${sentences_basename}.${parser}.answer \
      2> ${results_dir}/${sentences_basename}.${parser}.err
  rte_answer=`cat ${results_dir}/${sentences_basename}.${parser}.answer`
  echo "judging entailment for ${parsed_dir}/${sentences_basename}.${parser}.sem.xml $rte_answer"
  proof_end_time=`python -c 'import time; print(time.time())'`
  proving_time=`echo "${proof_end_time} - ${start_time}" | bc -l | \
       awk '{printf("%.2f\n",$1)}'`
  echo $proving_time > ${results_dir}/${sentences_basename}.time
}

function select_answer() {
  parser=$1
  fname=${results_dir}/${sentences_basename}.${parser}.answer
  if [ ! -e $fname ]; then
    echo "" > $fname
  fi
  fname_answer=`cat ${fname}`
  if [ "current_answer" = "no" ] && [ "$fname_answer" = "yes" ]; then
    current_answer="unknown"
  elif [ "current_answer" = "yes" ] && [ "$fname_answer" = "no" ]; then
    current_answer="unknown"
  elif [ "$fname_answer" = "yes" ]; then
    current_answer="yes"
    prediction_fname=`echo ${fname##*/} | sed 's/.answer//g'`
  elif [ "$fname_answer" = "no" ]; then
    current_answer="no"
    prediction_fname=`echo ${fname##*/} | sed 's/.answer//g'`
  else
    :
  fi
  if [ ! -z "${prediction_fname}" ]; then
    cp ${parsed_dir}/${prediction_fname}.jigg.xml ${parsed_dir}/${sentences_basename}.xml
    cp ${parsed_dir}/${prediction_fname}.sem.xml ${parsed_dir}/${sentences_basename}.sem.xml
    cp ${results_dir}/${prediction_fname}.answer ${results_dir}/${sentences_basename}.answer
    cp ${results_dir}/${prediction_fname}.html ${results_dir}/${sentences_basename}.html
  fi
}

# Set the current answer
current_answer="unknown"
prediction_fname="${sentences_basename}.jigg"

# CCG parsing, semantic parsing and theorem proving
for parser in `cat ja/parser_location_ja.txt`; do
  parser_name=`echo $parser | awk -F':' '{print $1}'`
  parser_dir=`echo $parser | awk -F':' '{print $2}'`
  if [ ! -e ${parsed_dir}/${sentences_basename}.${parser_name}.jigg.xml ]; then
    echo "${parser_name} parsing ${plain_dir}/${sentences_basename}"
    parse_$parser_name $sentences_basename
  fi
  if [ ! -e ${parsed_dir}/${sentences_basename}.${parser_name}.sem.xml ]; then
    echo "semantic parsing $parsed_dir/${sentences_basename}.${parser_name}.sem.xml"
    semantic_parsing $parser_name $sentences_basename
  fi
  if [ ! -e ${results_dir}/${sentences_basename}.${parser_name}.answer ]; then
    proving $parser_name $sentences_basename
    select_answer ${parser_name}
  fi
  if [ ! -e ${results_dir}/${sentences_basename}.${parser_name}.answer ]; then
    python scripts/visualize.py ${parsed_dir}/${sentences_basename}.${parser_name}.sem.xml \
    > ${results_dir}/${sentences_basename}.${parser_name}.html
  fi
done
