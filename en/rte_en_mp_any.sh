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

# Script to Recognize Textual Entailment of problems in English, using
# multiple CCG parsers (C&C and EasyCCG at the moment).
# This script receives a file with several sentences (one per line), where all
# sentences are premises except the last one, which is a conclusion. It returns
# 'yes' (the premises entail the conclusion), 'no' (there is a contradiction) or
# 'unknown' (none of the former).
# You can use it as:
# 
# ./rte_en_mp_any.sh <sentences.txt> <semantic_templates.yaml> <nbest>
# 
# E.g.
# ./rte_en_mp_any.sh en/sample_en.txt en/semantic_templates_en.yaml 3

USAGE="Usage: ./rte_en_mp_any.sh <sentences.txt> <semantic_templates.yaml> <nbest>"

# Set the number of nbest parses (Default: 1)
nbest=${3:-1}

# Create a file named "parser_location.txt" at the "en" directory and
# write a list of CCG parsers installed, as in:
# $ cat en/parser_location.txt
# candc:/path/to/candc-1.00
# easyccg:/path/to/easyccg
# easysrl:/path/to/EasySRL
# depccg:/path/to/depccg

# # Check that the number of arguments is correct.
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

function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="en_plain" # tokenized sentences.
parsed_dir="en_parsed" # parsed sentences into XML or other formats.
results_dir="en_results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Tokenize text with Penn Treebank tokenizer.
cat $sentences_fname | \
  sed -f en/tokenizer.sed | \
  sed 's/ _ /_/g' | \
  sed 's/[[:space:]]*$//' \
  > ${plain_dir}/${sentences_basename}.tok

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
  if [ "${parser_name}" == "easysrl" ]; then
    easysrl_dir=${parser_dir}
    if [ ! -d "${easysrl_dir}" ] || [ ! -e "${easysrl_dir}"/easysrl.jar ]; then
      echo "EasySRL parser directory incorrect. Exit."
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

function parse_candc() {
  # Parse using C&C.
  base_fname=$1
  ${candc_dir}/bin/candc \
      --models ${candc_dir}/models \
      --candc-printer xml \
      --input ${plain_dir}/${base_fname}.tok \
    2> ${parsed_dir}/${base_fname}.log \
     > ${parsed_dir}/${base_fname}.candc.xml
  python en/candc2transccg.py ${parsed_dir}/${base_fname}.candc.xml \
    > ${parsed_dir}/${base_fname}.candc.jigg.xml \
    2> ${parsed_dir}/${base_fname}.log
}

function parse_candc_question() {
  # Parse using C&C.
  base_fname=$1
  ${candc_dir}/bin/candc \
      --models ${candc_dir}/models/questions \
      --candc-printer xml \
      --input ${plain_dir}/${base_fname}.tok \
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
    --maxLength 100 \
    --nbest "${nbest}" \
    > ${parsed_dir}/${base_fname}.easyccg \
    2> ${parsed_dir}/${base_fname}.easyccg.log
  python en/easyccg2jigg.py \
    ${parsed_dir}/${base_fname}.easyccg \
    ${parsed_dir}/${base_fname}.easyccg.jigg.xml \
    2> ${parsed_dir}/${base_fname}.easyccg.xml.log
}

function parse_easyccg_question() {
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
    --model ${easyccg_dir}/model_questions -s -r S[q] S[qem] S[wq] \
    -i POSandNERtagged \
    -o extended \
    --maxLength 100 \
    --nbest "${nbest}" \
    > ${parsed_dir}/${base_fname}.easyccg \
    2> ${parsed_dir}/${base_fname}.easyccg.log
  python en/easyccg2jigg.py \
    ${parsed_dir}/${base_fname}.easyccg \
    ${parsed_dir}/${base_fname}.easyccg.jigg.xml \
    2> ${parsed_dir}/${base_fname}.easyccg.xml.log
}

function parse_easysrl() {
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
  java -jar ${easysrl_dir}/easysrl.jar \
    --model ${easysrl_dir}/model \
    -o extended \
    -i POSandNERtagged \
    --nbest "${nbest}" \
    > ${parsed_dir}/${base_fname}.easysrl \
    2> ${parsed_dir}/${base_fname}.easysrl.log
  python en/easyccg2jigg.py \
    ${parsed_dir}/${base_fname}.easysrl \
    ${parsed_dir}/${base_fname}.easysrl.jigg.xml \
    2> ${parsed_dir}/${base_fname}.easysrl.xml.log
}

function lemmatize() {
    # apply easyccg's lemmatizer to input file
    input_file=$1
    lemmatized=`mktemp -t tmp-XXX`
    cat $input_file | java -cp ${easyccg_dir}/easyccg.jar \
        uk.ac.ed.easyccg.lemmatizer.MorphaStemmer \
        > $lemmatized \
        2>/dev/null
    paste -d "|" $input_file $lemmatized | \
        awk '{split($0, res, "|");
             slen = split(res[1], sent1);split(res[2], sent2);
             for (i=1; i <= slen; i++) {
                printf sent1[i] "|" sent2[i]
                if (i < slen) printf " "
            }; print ""}'
}

function parse_depccg() {
    # Parse using depccg.
    base_fname=$1
    lemmatize ${plain_dir}/${base_fname}.tok | \
    ${candc_dir}/bin/pos \
        --model ${candc_dir}/models/pos \
        --ifmt "%w|%l \n" \
        --ofmt "%w|%l|%p \n" \
        2> /dev/null | \
    ${candc_dir}/bin/ner \
        --model ${candc_dir}/models/ner \
        --ifmt "%w|%l|%p \n" \
        --ofmt "%w|%l|%p|%n \n" \
        2> /dev/null | \
    python ${depccg_dir}/src/run.py \
        ${depccg_dir}/models/tri_headfirst \
        en \
        --input-format POSandNERtagged \
        --format xml \
    2> ${parsed_dir}/${base_fname}.depccg.xml.log \
    > ${parsed_dir}/${base_fname}.depccg.xml
  python en/candc2transccg.py ${parsed_dir}/${base_fname}.depccg.xml \
    > ${parsed_dir}/${base_fname}.depccg.jigg.xml \
    2> ${parsed_dir}/${base_fname}.log
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
      --abduction spsa \
      > ${results_dir}/${sentences_basename}.${parser}.answer \
      2> ${results_dir}/${sentences_basename}.${parser}.err
  rte_answer=`cat ${results_dir}/${sentences_basename}.${parser}.answer`
  echo "judging entailment ${parsed_dir}/${sentences_basename}.${parser}.sem.xml $rte_answer"
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
prediction_fname="${sentences_basename}.candc"

# CCG parsing, semantic parsing and theorem proving
for parser in `cat en/parser_location.txt`; do
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
