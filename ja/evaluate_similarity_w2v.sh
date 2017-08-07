#!/bin/bash
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

#run word2vec-api for Japanese
nohup python ../word2vec-api/word2vec-api.py --model entity_vector.model.txt 2>&1 &
while :
do
  testsim=$(curl http://localhost:5000/word2vec/similarity?w1=の\&w2=が)
  if [ `echo $testsim| grep '0.541'` ]; then
    echo "word2vec-api started"
    break
  fi
  sleep 100
done

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

plain_dir=ja_plain
results_dir=ja_results

# Usage: 
#
# ./en/evaluate_similarity_sick.sh 3 trial en/semantic_templates_en_event.yaml (word2vec)
#

# Extract training and test data from SICK dataset, removing the header line.
if [ ! -d ${plain_dir} ]; then
  mkdir -p ${plain_dir}
fi

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

rm ${plain_dir}/sick_{train,test,trial}.files_??
split -l $train_lines_per_split ${plain_dir}/sick_train.files ${plain_dir}/sick_train.files_
split -l $test_lines_per_split ${plain_dir}/sick_test.files ${plain_dir}/sick_test.files_
split -l $trial_lines_per_split ${plain_dir}/sick_trial.files ${plain_dir}/sick_trial.files_

# Copy a coq static library and compile it
cp ja/coqlib_ja.v coqlib.v
coqc coqlib.v
cp ja/tactics_coq.txt tactics_coq.txt

#nohup ./removecore.sh 2>&1 &

# Run pipeline for each entailment problem.
for ff in ${plain_dir}/sick_${dataset}.files_??; do
  for f in `cat ${ff}`; do
    #./en/similarity_en_mp_w2v.sh $f $templates;
    ./ja/similarity_ja_mp.sh $f $templates word2vec;
  done &
done

# Wait for the parallel processes to finish.
wait

# gold_dir=$1
# sys_dir=$2
 
total=0
correct=0
for f in ./ja_plain2/sick_${dataset}_*.answer; do
  let total++
  base_filename=${f##*/}
  sys_filename=./ja_results/${base_filename}
  gold_answer=`head -1 $f`
  if [ ! -e ${sys_filename} ]; then
    sys_answer="unknown"
  else
    sys_answer=`head -1 ${sys_filename}`
  fi
  echo -e $f"\t"$gold_answer"\t"$sys_answer
done

plain_dir2=ja_plain

# Print a summary (precision, recall, f-score) of the errors at individual problems,
# per problem category and a global score.
echo "Evaluating."
echo "<!doctype html>
<html lang='ja'>
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
for gold_filename in `ls -v ${plain_dir2}/sick_${dataset}_*.answer`; do
  base_filename=${gold_filename##*/} # this line obtains the filename, without the directory path.
  system_filename=${results_dir}/${base_filename/.txt/.answer}
  gold_answer=`cat $gold_filename`
  system_answer=`cat $system_filename`
  time_filename=${results_dir}/${base_filename/.answer/.time}
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
  <td><a style="background-color:'$color';" href="'${base_filename/.answer/.html}'">'${base_filename/.answer/}'</a></td>
  <td>'$gold_answer'</td>
  <td>'$system_answer'</td>
  <td>'$proving_time's</td>
</tr>' >> $results_dir/main_${dataset}.html
done
average_proving_time=`echo "scale=2; $total_proving_time / $total_number" | bc -l`
echo "
<h4><font color="red">Average proving time: "${average_proving_time}" </font></h4>
</body>
</html>
" >> $results_dir/main_${dataset}.html

#./accuracy.sh ${results_dir}/main_${dataset}.html > ${results_dir}/score.txt

processid=$(ps ax|grep "word2vec-api.py"|grep -v grep|awk '{print $1}')
kill $processid

