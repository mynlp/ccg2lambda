#!/bin/bash

# Usage
#  ./evaluate_dataset <cores> <split>
#
# <split> ::= test | train
#
# Example:
#
# ./en/evaluate_dataset.sh 10 train
#
# <en_plain> ::= en_plain_smt | en_plain_par | en_plain_vid
# <en_parsed> ::= en_parsed_smt | en_parsed_par | en_parsed_vid
#

cores=${1:-3}
dataset=${2:-"train"}
templates="semantic_templates_en_event_vertical.yaml"

plain_dir="en_plain"
parsed_dir="en_parsed"
results_dir="en_results"
mkdir -p $plain_dir $results_dir

ls -v ${plain_dir}/sick_${dataset}_*.txt > ${plain_dir}/sick_${dataset}.files

ndata=`cat ${plain_dir}/sick_${dataset}.files | wc -l`
lines_per_split=`python -c "from math import ceil; print(int(ceil(float(${ndata})/${cores})))"`

rm -f ${plain_dir}/sick_${dataset}.files_??
split -l $lines_per_split ${plain_dir}/sick_${dataset}.files ${plain_dir}/sick_${dataset}.files_

# Copy a coq static library and compile it
cp en/coqlib_sick.v coqlib.v
coqc coqlib.v
cp en/tactics_coq_sick.txt tactics_coq.txt

# Run pipeline for each entailment problem.
for ff in ${plain_dir}/sick_${dataset}.files_??; do
  for f in `cat ${ff}`; do
    ./en/rte_en_mp_any.sh $f en/$templates
  done &
done

# Wait for the parallel processes to finish.
wait

echo "Evaluating."
echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results </title>
  <style>
    body {
      font-size: 1.5em;
    }
  </style>
</head>
<body>
<table border='1'>
<tr>
  <td>Problem</td>
  <td>C&C</td>
  <td>EasyCCG</td>
  <td>depccg</td>
</tr>" > $results_dir/main_${dataset}.html

total_observations=0
correct_recognitions=0
attempts=0
total_proving_time=0

red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"

for gold_filename in `ls -v ${plain_dir}/sick_${dataset}_*.txt`; do
  base_filename=${gold_filename##*/}
  # candc
  if [ -e ${results_dir}/${base_filename}.candc.answer ]; then
    candc_answer=`cat ${results_dir}/${base_filename}.candc.answer`
  else
    candc_answer="error"
  fi
  if [ -e ${parsed_dir}/${base_filename}.candc.cat.err ]; then
    candc_cat=`cat ${parsed_dir}/${base_filename}.candc.cat.err`
  fi
  # easyccg
  if [ -e ${results_dir}/${base_filename}.easyccg.answer ]; then
    easyccg_answer=`cat ${results_dir}/${base_filename}.easyccg.answer`
  else
    easyccg_answer="error"
  fi
  if [ -e ${parsed_dir}/${base_filename}.easyccg.cat.err ]; then
    easyccg_cat=`cat ${parsed_dir}/${base_filename}.easyccg.cat.err`
  fi
  # depccg
  if [ -e ${results_dir}/${base_filename}.depccg.answer ]; then
    depccg_answer=`cat ${results_dir}/${base_filename}.depccg.answer`
  else
    depccg_answer="error"
  fi
  if [ -e ${parsed_dir}/${base_filename}.depccg.cat.err ]; then
    depccg_cat=`cat ${parsed_dir}/${base_filename}.depccg.cat.err`
  fi
  echo '
<tr>
  <td>'$base_filename'</a></td>
  <td><a style="background-color:'$color';" href="'${base_filename}.candc.html'">'$candc_answer $candc_cat'</a></td>
  <td><a style="background-color:'$color';" href="'${base_filename}.easyccg.html'">'$easyccg_answer $easyccg_cat'</a></td>
  <td><a style="background-color:'$color';" href="'${base_filename}.depccg.html'">'$depccg_answer $depccg_cat'</a></td>
</tr>' >> $results_dir/main_${dataset}.html
done
echo "
</body>
</html>
" >> $results_dir/main_${dataset}.html
