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

# Usage: 
#
# ./en/eacl2017exp.sh <ncores> <split> <templates.yaml>
#
# Example:
#
# ./en/eacl2017exp.sh 10 train en/semantic_templates_en_event.yaml
#

source /data/pascual/anaconda2/envs/py3/bin/activate

category_templates=en/semantic_templates_en_event_flat.yaml
# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="plain" # tokenized sentences.
parsed_dir="parsed" # parsed sentences into XML or other formats.
results_dir="results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir
parsers="easyccg candc"

# multinli=multinli/multinli_0.9_train.jsonl
# sentences_basename=multinli

# Convert SICK.semeval.txt dataset into SNLI jsonl format.
if [ ! -e en/sick.trial.jsonl ] || [ ! -e en/sick.train.jsonl ] || [ ! -e en/sick.test.jsonl ] ; then
  echo "Preparing SICK dataset."
  sed -i "s///" en/SICK.semeval.txt
  grep TRIAL en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.trial.jsonl
  grep TRAIN en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.train.jsonl
  grep TEST en/SICK.semeval.txt | python scripts/sick2snli.py > en/sick.test.jsonl
fi

sentences_basename="sick.trial"
multinli=en/${sentences_basename}.jsonl
python scripts/get_nli_sentences.py \
    $multinli \
    > ${plain_dir}/${sentences_basename}.tok

function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }

# Tokenize text with Penn Treebank tokenizer.
# cat ${plain_dir}/${sentences_basename}.txt | \
#   sed -f en/tokenizer.sed | \
#   sed 's/ _ /_/g' | \
#   sed 's/[[:space:]]*$//' \
#   > ${plain_dir}/${sentences_basename}.tok

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
    --nbest 1 \
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
    echo -n "Proving for $rte_fname "
    python scripts/prove.py \
      $rte_fname \
      --proof ${rte_fname/rte/proof} \
      --abduction spsa \
      --ncores 200 \
      2> ${rte_fname/rte/proof}.log
    echo
  done
done

exit

# How many processes in parallel you want to run.
# The maximum number should be inferior to the number of cores in your machine.
# Default: 3
cores=${1:-3}
templates=$category_templates

# Copy a coq static library and compile it.
cp en/coqlib_sick.v coqlib.v
coqc coqlib.v
cp en/tactics_coq_sick.txt tactics_coq.txt

# Run pipeline for each entailment problem.
for ff in ${plain_dir}/sick_${dataset}.files_??; do
  for f in `cat ${ff}`; do
    ./en/rte_en_mp.sh $f $templates;
  done &
done

# Wait for the parallel processes to finish.
wait

total=0
correct=0
for f in ${plain_dir}/sick_${dataset}_*.answer; do
  let total++
  base_filename=${f##*/}
  sys_filename=${results_dir}/${base_filename/.answer/.txt.answer}
  gold_answer=`head -1 $f`
  if [ ! -e ${sys_filename} ]; then
    sys_answer="unknown"
  else
    sys_answer=`head -1 ${sys_filename}`
    if [ ! "${sys_answer}" == "unknown" ] && [ ! "${sys_answer}" == "yes" ] && [ ! "${sys_answer}" == "no" ]; then
      sys_answer="unknown"
    fi
  fi
  if [ "${gold_answer}" == "${sys_answer}" ]; then
    let correct++
  fi
  echo -e $f"\t"$gold_answer"\t"$sys_answer
done

accuracy=`echo "scale=3; $correct / $total" | bc -l`
echo "Accuracy: "$correct" / "$total" = "$accuracy

# Print a summary (precision, recall, f-score) of the errors at individual problems,
# per problem category and a global score.
echo "Evaluating."
echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results of "$category_templates"</title>
  <style>
    body {
      font-size: 1.5em;
    }
  </style>
</head>
<body>
<table border='1'>
<tr>
  <td>sick problem</td>
  <td>gold answer</td>
  <td>system answer</td>
  <td>proving time</td>
</tr>" > $results_dir/main_${dataset}.html
total_observations=0
correct_recognitions=0
attempts=0
total_proving_time=0
red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"
for gold_filename in `ls -v ${plain_dir}/sick_${dataset}_*.answer`; do
  base_filename=${gold_filename##*/} # this line obtains the filename, without the directory path.
  system_filename=${results_dir}/${base_filename/.answer/.txt.answer}
  gold_answer=`cat $gold_filename`
  system_answer=`cat $system_filename`
  time_filename=${results_dir}/${base_filename/.answer/.txt.time}
  proving_time=`cat $time_filename`
  total_proving_time=`echo "$total_proving_time + $proving_time" | bc -l`
  total_number=$((total_number + 1))
  color=$white_color
  if [ "$gold_answer" == "yes" ] || [ "$gold_answer" == "no" ]; then
    total_observations=$((total_observations + 1))
    if [ "$gold_answer" == "$system_answer" ]; then
      correct_recognitions=$((correct_recognitions + 1))
      color=$green_color
    else
      color=$red_color
    fi
    if [ "$system_answer" == "yes" ] || [ "$system_answer" == "no" ]; then
      attempts=$((attempts + 1))
    else
      color=$gray_color
    fi
  fi
  echo '
<tr>
  <td><a style="background-color:'$color';" href="'${base_filename/.answer/.txt.html}'">'${base_filename/.answer/}'</a></td>
  <td>'$gold_answer'</td>
  <td>'$system_answer'</td>
  <td>'$proving_time's</td>
</tr>' >> $results_dir/main_${dataset}.html
done
average_proving_time=`echo "scale=2; $total_proving_time / $total_number" | bc -l`
echo "
<h4><font color="red">Accuracy: "$correct" / "$total" = "$accuracy" </font></h4>
<h4><font color="red">Average proving time: "${average_proving_time}" </font></h4>
</body>
</html>
" >> $results_dir/main_${dataset}.html

./ja/accuracy.sh ${results_dir}/main_${dataset}.html > ${results_dir}/score.txt
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
# ./rte_en_mp.sh <sentences.txt> <semantic_templates.yaml>
# 
# E.g.
# ./rte_en_mp.sh en/sample_en.txt en/semantic_templates_en.yaml
#
# It should return 'yes'.
# You need to have a file in the current directory named candc_location.txt
# where you have the absolute directory path to C&C parser.
# Inside the directory pointed by candc_location.txt, there should be
# a directory called "bin" that contains the binaries of C&C parser
# and another directory called "models" that contains the models.
# For example:
# $ cat en/candc_location.txt
#   /home/pasmargo/software/candc/candc-1.00

USAGE="Usage: ./rte_en_mp.sh <sentences.txt> <semantic_templates.yaml>"

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

function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir="plain" # tokenized sentences.
parsed_dir="parsed" # parsed sentences into XML or other formats.
results_dir="results" # HTML semantic outputs, proving results, etc.
mkdir -p $plain_dir $parsed_dir $results_dir

# Tokenize text with Penn Treebank tokenizer.
# cat $sentences_fname | \
#   sed -f en/tokenizer.sed | \
#   sed 's/ _ /_/g' | \
#   sed 's/[[:space:]]*$//' \
#   > ${plain_dir}/${sentences_basename}.tok

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
    2> ${parsed_dir}/${base_fname}.easyccg.jigg.log
}

if [ ! -e ${parsed_dir}/${sentences_basename}.xml ]; then
  echo "Syntactic parsing ${plain_dir}/${sentences_basename}.tok"
  parse_candc ${sentences_basename}
  parse_easyccg ${sentences_basename}
fi

# Semantic parsing the CCG trees in XML.
if [ ! -e "$parsed_dir/${sentences_basename}.sem.xml" ]; then
  for parser in "candc" "easyccg"; do
    if [ ! -e "$parsed_dir/${sentences_basename}.${parser}.sem.xml" ]; then
      echo "Semantic parsing $parsed_dir/${sentences_basename}.${parser}.jigg.xml"
      python scripts/semparse.py \
        $parsed_dir/${sentences_basename}.${parser}.jigg.xml \
        $category_templates \
        $parsed_dir/${sentences_basename}.${parser}.sem.xml \
        --arbi-types \
        2> $parsed_dir/${sentences_basename}.${parser}.sem.err
    fi
  done
fi

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
    answer1=`cat ${answer1_fname}`
    answer2=`cat ${answer2_fname}`
    if [ "$answer1" != "unknown" ] && ([ "$answer2" == "unknown" ] || [ "$answer2" == "" ]); then
      prediction_fname=$base_fname1
    elif ([ "$answer1" == "unknown" ] || [ "$answer1" == "" ]) && [ "$answer2" != "unknown" ]; then
      prediction_fname=$base_fname2
    else
      prediction_fname=$base_fname1
    fi
  fi
  if [ ! -z "${prediction_fname}" ]; then
    cp ${parsed_dir}/${prediction_fname}.jigg.xml ${parsed_dir}/${sentences_basename}.xml
    cp ${parsed_dir}/${prediction_fname}.sem.xml ${parsed_dir}/${sentences_basename}.sem.xml
    cp ${results_dir}/${prediction_fname}.answer ${results_dir}/${sentences_basename}.answer
    cp ${results_dir}/${prediction_fname}.html ${results_dir}/${sentences_basename}.html
  fi
}

# Judge entailment with a theorem prover (Coq, at the moment).
if [ ! -e "${results_dir}/${sentences_basename/.tok/.answer}" ]; then
  start_time=`python -c 'import time; print(time.time())'`
  for parser in "candc" "easyccg"; do
    if [ ! -e "${results_dir}/${sentences_basename}.${parser}.answer" ]; then
      timeout 100 python scripts/prove.py \
        $parsed_dir/${sentences_basename}.${parser}.sem.xml \
        --graph_out ${results_dir}/${sentences_basename}.${parser}.html \
        --abduction spsa \
        > ${results_dir}/${sentences_basename}.${parser}.answer \
        2> ${results_dir}/${sentences_basename}.${parser}.err
    fi
    rte_answer=`cat ${results_dir}/${sentences_basename}.${parser}.answer`
    echo "Judged entailment for $parsed_dir/${sentences_basename}.${parser}.sem.xml $rte_answer"
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

