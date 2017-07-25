#!/bin/bash
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

# Script to extract features for learning semantic textual similarity between sentence pairs in English, using
# multiple CCG parsers (C&C and EasyCCG at the moment).
# This script receives a file with two sentences (one per line).
# You can use it as:
# 
# ./similarity_en_mp_any.sh <sentences.txt> <semantic_templates.yaml>
# 
# E.g.
# ./similarity_en_mp_any.sh en/sample_en.txt en/semantic_templates_en_event_sts.yaml
#
# You need to have a file in the current directory named parser_location.txt
# where you have the absolute directory path to C&C parser and EasyCCG parser.
# Inside the directory pointed by parser_location.txt, there should be
# a directory called "bin" that contains the binaries of C&C parser
# and another directory called "models" that contains the models.
# For example:
# $ cat en/parser_location.txt
# candc:/home/usr/software/candc/candc-1.00
# easyccg:/home/usr/software/easyccg

USAGE="Usage: ./similarity_en_mp_any.sh <sentences.txt> <semantic_templates.yaml>"

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
sentences_basename=${sentences_basename/.txt/}
if [ ! -f $sentences_fname ]; then
  echo "Error: File with plain sentences does not exist."
  echo $USAGE
  exit 1
fi

#word2vec flag
word2vec=$3

function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="plain" # tokenized sentences.
parsed_dir="parsed" # parsed sentences into XML or other formats.
results_dir="results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Tokenize text with Penn Treebank tokenizer.
if [ ! -f ${plain_dir}/${sentences_basename}.tok ]; then
  cat $sentences_fname | \
    sed -f en/tokenizer.sed | \
    sed 's/ _ /_/g' | \
    sed 's/[[:space:]]*$//' \
    > ${plain_dir}/${sentences_basename}.tok
fi

# Set parser locations
if [ ! -f "en/parser_location.txt" ]; then
  echo "Error: File for the locations of parsers does not exist."
  exit 1
fi
for parser in `cat en/parser_location.txt`; do
  parser_name=`echo $parser | awk -F':' '{print $1}'`
  parser_dir=`echo $parser | awk -F':' '{print $2}'`
  if [ "${parser_name}" == "candc" ]; then
    candc_dir=${parser_dir}
    if [ ! -d "${candc_dir}" ] || [ ! -e "${candc_dir}"/bin/candc ]; then
      echo "C&C parser directory incorrect. Exit."
      exit 1
    fi
  fi
  if [ "${parser_name}" == "easyccg" ]; then
    easyccg_dir=${parser_dir}
    if [ ! -d "${easyccg_dir}" ] || [ ! -e "${easyccg_dir}"/easyccg.jar ]; then
      echo "EasyCCG parser directory incorrect. Exit."
      exit 1
    fi
  fi
done


function parse_candc() {
  # Parse using C&C.
  base_fname=$1
  ${candc_dir}/bin/candc \
      --models ${candc_dir}/models \
      --candc-printer xml \
      --input $parser_cmd ${plain_dir}/${base_fname}.tok \
    2> ${parsed_dir}/${base_fname}.log \
     > ${parsed_dir}/${base_fname}.candc.xml
  python en/candc2transccg.py ${parsed_dir}/${base_fname}.candc.xml \
    > ${parsed_dir}/${base_fname}.candc.jigg.xml \
    2> ${parsed_dir}/${base_fname}.log
}

function parse_easyccg() {
  # Parse using EasyCCG.
  base_fname=$1
  cat ${plain_dir}/${base_fname}.tok | \
  ${candc_dir}/bin/pos \
    --model ${candc_dir}/models/pos \
    2>/dev/null | \
  ${candc_dir}/bin/ner \
    -model ${candc_dir}/models/ner \
    -ofmt "%w|%p|%n \n" \
    2>/dev/null | \
  java -jar ${easyccg_dir}/easyccg.jar \
    --model ${easyccg_dir}/model \
    -i POSandNERtagged \
    -o extended \
    --nbest 1 \
    > ${parsed_dir}/${base_fname}.easyccg \
    2> ${parsed_dir}/${base_fname}.easyccg.log
  python en/easyccg2jigg.py \
    ${parsed_dir}/${base_fname}.easyccg \
    ${parsed_dir}/${base_fname}.easyccg.jigg.xml \
    2> ${parsed_dir}/${base_fname}.xml.log
}


function select_answer() {
  answer1_fname=$1
  answer2_fname=$2
  base_fname1=`echo ${answer1_fname##*/} | sed 's/.answer//g'`
  base_fname2=`echo ${answer2_fname##*/} | sed 's/.answer//g'`
  sentences_basename=${base_fname1/.candc/}
  if [ ! -e $answer1_fname ] && [ ! -e $answer2_fname ]; then
    echo "unknown" > ${answer1_fname/.candc/};
    prediction_fname=""
  elif [ ! -e $answer1_fname ]; then
    prediction_fname=$base_fname2
  elif [ ! -e $answer2_fname ]; then
    prediction_fname=$base_fname1
  elif [ -e $answer1_fname ] && [ -e $answer2_fname ]; then
    gold_file=${answer1_fname/results/plain}
    gold_answer=`cat ${gold_file/.candc/}` #gold
    if [ "$gold_answer" == "yes" ]; then
      gold_answer="1"
    elif [ "$gold_answer" == "no" ]; then
      gold_answer="0.5"
    elif [ "$gold_answer" == "unknown" ]; then
      gold_answer="0"
    fi
    answer1=`cat ${answer1_fname}|tr -d '\r'|awk -F , 'NR == 1 {print $1}'` #candc
    answer1=${answer1/\[}
    answer2=`cat ${answer2_fname}|tr -d '\r'|awk -F , 'NR == 1 {print $1}'` #easyccg
    answer2=${answer2/\[}
    #check gold answer
    if [ "$gold_answer" == "$answer1" ]; then
      prediction_fname=$base_fname1 #candc
    elif [ "$gold_answer" == "$answer2" ]; then
      prediction_fname=$base_fname2 #easyccg
    fi
  fi

  if [ ! -z "${prediction_fname}" ]; then
    cp ${parsed_dir}/${prediction_fname}.jigg.xml ${parsed_dir}/${sentences_basename}.xml
    cp ${parsed_dir}/${prediction_fname}.sem.xml ${parsed_dir}/${sentences_basename}.sem.xml
    cp ${results_dir}/${prediction_fname}.answer ${results_dir}/${sentences_basename}.answer
    cp ${results_dir}/${prediction_fname}.html ${results_dir}/${sentences_basename}.html
  fi
}


if [ ! -e ${parsed_dir}/${sentences_basename}.xml ]; then
  echo "Syntactic parsing ${plain_dir}/${sentences_basename}.tok"
  parse_candc ${sentences_basename}
  parse_easyccg ${sentences_basename}
fi

# Semantic parsing the CCG trees in XML.
if [ ! -e "$parsed_dir/${sentences_basename}.sem.xml" ]; then
  for parser in `cat en/parser_location.txt`; do
    parser_name=`echo $parser | awk -F':' '{print $1}'`
    if [ ! -e "$parsed_dir/${sentences_basename}.${parser_name}.sem.xml" ]; then
      echo "Semantic parsing $parsed_dir/${sentences_basename}.${parser_name}.jigg.xml"
      python scripts/semparse.py \
        $parsed_dir/${sentences_basename}.${parser_name}.jigg.xml \
        $category_templates \
        $parsed_dir/${sentences_basename}.${parser_name}.sem.xml \
        --arbi-types \
        2> $parsed_dir/${sentences_basename}.${parser_name}.sem.err
    fi
  done
fi

# Judge entailment with a theorem prover (Coq, at the moment).
if [ ! -e "${results_dir}/${sentences_basename/.tok/.answer}" ]; then
  start_time=`python -c 'import time; print(time.time())'`
  for parser in `cat en/parser_location.txt`; do
    parser_name=`echo $parser | awk -F':' '{print $1}'`
    if [ ! -e "${results_dir}/${sentences_basename}.${parser_name}.answer" ]; then
      if [ "$word2vec" == "word2vec" ]; then
        timeout 600 python scripts/prove_w2v.py \
          $parsed_dir/${sentences_basename}.${parser_name}.sem.xml \
          --graph_out ${results_dir}/${sentences_basename}.${parser_name}.html \
          --abduction \
          --similarity \
          > ${results_dir}/${sentences_basename}.${parser_name}.answer \
          2> ${results_dir}/${sentences_basename}.${parser_name}.err
      else
        timeout 600 python scripts/prove.py \
          $parsed_dir/${sentences_basename}.${parser_name}.sem.xml \
          --graph_out ${results_dir}/${sentences_basename}.${parser_name}.html \
          --abduction \
          --similarity \
          > ${results_dir}/${sentences_basename}.${parser_name}.answer \
          2> ${results_dir}/${sentences_basename}.${parser_name}.err
      fi
    fi
    rte_answer=`cat ${results_dir}/${sentences_basename}.${parser_name}.answer`
    echo "Judged entailment for $parsed_dir/${sentences_basename}.${parser_name}.sem.xml $rte_answer"
  done
  proof_end_time=`python -c 'import time; print(time.time())'`
  proving_time=`echo "${proof_end_time} - ${start_time}" | bc -l | \
       awk '{printf("%.2f\n",$1)}'`
  echo $proving_time > ${results_dir}/${sentences_basename}.time
  select_answer \
    ${results_dir}/${sentences_basename}.candc.answer \
    ${results_dir}/${sentences_basename}.easyccg.answer
fi
echo "Judged entailment for $parsed_dir/${sentences_basename}.sem.xml "`cat ${results_dir}/${sentences_basename}.answer`
