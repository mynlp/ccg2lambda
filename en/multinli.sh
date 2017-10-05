#!/bin/bash
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

# Usage: 
#
# ./en/multinli.sh
#

source python_env.sh

# Copy coq static library and compile it.
cp en/coqlib_sick.v coqlib.v
coqc coqlib.v
cp en/tactics_coq_sick.txt tactics_coq.txt

category_templates=en/semantic_templates_en_event.yaml
# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="plain" # tokenized sentences.
parsed_dir="parsed" # parsed sentences into XML or other formats.
results_dir="results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir
# parsers="easyccg candc"
parsers="candc"
ncores=200

# multinli=multinli/multinli_0.9_train.jsonl
# sentences_basename=multinli

# Convert SICK.semeval.txt dataset into SNLI jsonl format.
# if [ ! -e en/sick.trial.jsonl ] || [ ! -e en/sick.train.jsonl ] || [ ! -e en/sick.test.jsonl ] ; then
#   echo "Preparing SICK dataset."
#   sed -i "s///" en/SICK.semeval.txt
#   grep TRIAL en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.trial.jsonl
#   grep TRAIN en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.train.jsonl
#   grep TEST en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.test.jsonl
# fi

# sentences_basename="snli.train"
sentences_basename="sick.trial"
multinli=en/${sentences_basename}.jsonl
python scripts/get_nli_sentences.py \
    $multinli \
    > ${plain_dir}/${sentences_basename}.tok

# Check whether the parser variables point to correct directories.
candc_dir=`cat en/candc_location.txt`
if [ ! -d "${candc_dir}" ] || [ ! -e "${candc_dir}"/bin/candc ]; then
  echo "C&C parser directory incorrect. Exit."
  exit 1
fi
easyccg_dir=`cat en/easyccg_location.txt`
if [ ! -d "${easyccg_dir}" ] || [ ! -e "${easyccg_dir}"/easyccg.jar ]; then
  echo "EasyCCG parser directory incorrect. Exit."
  exit 1
fi

function parse_candc() {
  # Parse using C&C.
  base_fname=$1
  ${candc_dir}/bin/candc \
      --models ${candc_dir}/models \
      --candc-printer xml \
      --input ${plain_dir}/${base_fname}.tok \
    2> ${parsed_dir}/${base_fname}.candc.log \
     > ${parsed_dir}/${base_fname}.candc.xml
  python en/candc2transccg.py ${parsed_dir}/${base_fname}.candc.xml \
    > ${parsed_dir}/${base_fname}.candc.jigg.xml \
    2> ${parsed_dir}/${base_fname}.candc.jigg.log
}

# function parse_easyccg() {
#   # Parse using EasyCCG.
#   base_fname=$1
#   cat ${plain_dir}/${base_fname}.tok | \
#   ${candc_dir}/bin/pos \
#     --model ${candc_dir}/models/pos \
#     --maxwords 410 | \
#   ${candc_dir}/bin/ner \
#     --model ${candc_dir}/models/ner \
#     --maxwords 410 \
#     --ofmt "%w|%p|%n \n" > ${parsed_dir}/multinli.ner
# }

function parse_easyccg() {
  # Parse using EasyCCG.
  base_fname=$1
  cat ${plain_dir}/${base_fname}.tok | \
  ${candc_dir}/bin/pos \
    --maxwords 410 \
    --model ${candc_dir}/models/pos \
    2>/dev/null | \
  ${candc_dir}/bin/ner \
    --maxwords 410 \
    --model ${candc_dir}/models/ner \
    --ofmt "%w|%p|%n \n" \
    2>/dev/null | \
  java -jar ${easyccg_dir}/easyccg.jar \
    --model ${easyccg_dir}/model \
    -i POSandNERtagged \
    -o extended \
    --nbest 2 \
    --maxLength 120 \
    > ${parsed_dir}/${base_fname}.easyccg \
    2> ${parsed_dir}/${base_fname}.easyccg.log
  python en/easyccg2jigg.py \
    ${parsed_dir}/${base_fname}.easyccg \
    ${parsed_dir}/${base_fname}.easyccg.jigg.xml \
    2> ${parsed_dir}/${base_fname}.easyccg.jigg.log
}

for parser in ${parsers}; do
  if [ ! -e ${parsed_dir}/${sentences_basename}.${parser}.jigg.xml ]; then
    echo "Syntactic $parser parsing ${plain_dir}/${sentences_basename}.tok"
    parse_$parser ${sentences_basename}
  fi
done

# Semantic parsing the CCG trees in XML.
if [ ! -e "$parsed_dir/${sentences_basename}.sem.xml" ]; then
  for parser in ${parsers}; do
    if [ ! -e "$parsed_dir/${sentences_basename}.${parser}.sem.xml" ]; then
      echo -n "Semantic parsing $parsed_dir/${sentences_basename}.${parser}.jigg.xml "
      python scripts/semparse.py \
        $parsed_dir/${sentences_basename}.${parser}.jigg.xml \
        $category_templates \
        $parsed_dir/${sentences_basename}.${parser}.sem.xml \
        --arbi-types \
        --ncores $ncores \
        2> $parsed_dir/${sentences_basename}.${parser}.sem.err
      echo
    fi
  done
fi

for parser in ${parsers}; do
  if [ ! -e "$parsed_dir/${sentences_basename}.${parser}.rte.xml" ]; then
    echo -n "Restructuring sentences into RTE problems for ${parser} "
      cat en/${sentences_basename}.jsonl | \
        python scripts/make_doc_labels.py \
        > en/${sentences_basename}.doc_labels.jsonl
      python scripts/restruct.py \
        $parsed_dir/${sentences_basename}.${parser}.sem.xml \
        $parsed_dir/${sentences_basename}.${parser}.rte.xml \
        --doc_labels en/${sentences_basename}.doc_labels.jsonl
    echo
  fi
done

for parser in ${parsers}; do
  for rte_fname in $parsed_dir/${sentences_basename}.${parser}.rte*.xml; do
    if [ ! -e ${rte_fname/rte/proof} ]; then
      echo -n "Proving for $rte_fname "
      python scripts/prove.py \
        $rte_fname \
        --proof ${rte_fname/rte/proof} \
        --abduction spsa \
        --ncores $ncores \
        2> ${rte_fname/rte/proof}.log
      echo
    fi
  done
done

for parser in ${parsers}; do
  echo "Evaluate on ${parser}:"
  python scripts/evaluate.py $parsed_dir/${sentences_basename}.${parser}.proof*.xml
done

