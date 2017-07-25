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

sick=en/SICK.semeval.txt

# How many processes in parallel you want to run.
# The maximum number should be inferior to the number of cores in your machine.
# Default: 3
cores=${1:-3}
# Split of the data (default train):
#   train (4439 problems),
#   test (4906 problems),
#   trial (495 problems).
dataset=${2:-"train"}
templates=$3

plain_dir=plain
results_dir=results

# Extract training and test data from SICK dataset, removing the header line.
if [ ! -d ${plain_dir} ]; then
  mkdir -p ${plain_dir}
fi

echo "Extracting problems from the SICK file."
tail -n +2 $sick | \
tr -d '\r' | \
awk -F'\t' -v tdir=${plain_dir} \
  '{pair_id=$1;
    sub(/\.$/,"",$2);
    sub(/\.$/,"",$3);
    premise=$2;
    conclusion=$3;
    if($5 == "CONTRADICTION"){
      judgement="no";
    } else if ($5 == "ENTAILMENT") {
      judgement="yes";
    } else if ($5 == "NEUTRAL") {
      judgement="unknown";
    }
    set=$NF;
    printf "%s.\n%s.\n", premise, conclusion > tdir"/sick_"tolower(set)"_"pair_id".txt";
    printf "%s\n", judgement > tdir"/sick_"tolower(set)"_"pair_id".answer";
   }'

# Create files that list all filenames of training, testing and trial.
for dset in {train,test,trial}; do
  ls -v ${plain_dir}/sick_${dset}_*.txt > ${plain_dir}/sick_${dset}.files
done
# Split filename entries into several files, for parallel processing:
ntrain=`cat ${plain_dir}/sick_train.files | wc -l`
ntest=`cat ${plain_dir}/sick_test.files | wc -l`
ntrial=`cat ${plain_dir}/sick_trial.files | wc -l`
train_lines_per_split=`python -c "from math import ceil; print(int(ceil(float(${ntrain})/${cores})))"`
test_lines_per_split=`python -c "from math import ceil; print(int(ceil(float(${ntest})/${cores})))"`
trial_lines_per_split=`python -c "from math import ceil; print(int(ceil(float(${ntrial})/${cores})))"`

rm -f ${plain_dir}/sick_{train,test,trial}.files_??
split -l $train_lines_per_split ${plain_dir}/sick_train.files ${plain_dir}/sick_train.files_
split -l $test_lines_per_split ${plain_dir}/sick_test.files ${plain_dir}/sick_test.files_
split -l $trial_lines_per_split ${plain_dir}/sick_trial.files ${plain_dir}/sick_trial.files_

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
