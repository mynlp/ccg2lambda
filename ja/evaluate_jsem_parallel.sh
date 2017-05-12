#!/bin/bash

# A script for paralell processing on jsem
#
# Usage:
#
# ./evaluate_jsem_tags.sh <number of cores> <tags>
#
# <tags> can be multiple:
#
# ./evaluate_jsem_tags.sh <number of cores> <tag1> <tag2> <-tag3>
#
# -tag3 means that tag3 is excluded
#
# tag := entailment | presupposition |
#        generalized quantifier | plural | ...

# Set how many processes in parallel you want to run.
# The maximum number should be inferior to the number of cores in your machine.
# Default: 3
cores=${1:-3}

# Set the semantic templates we want to evaluate:
templates="ja/semantic_templates_ja_emnlp2016.yaml"

################################################################
### extract problems by specified tags
### will be stored in "temp_jsem_problems_list"
################################################################
# Create a file containing a list of problems
# tagged with target phenomena and inference type
# Note: tag "verb" match with neither "adverb" nor "implicative verb",
#       since grep is called with "+verb"
# Note: we ignore uppler/lower case

# Create a temporary list from "jsem_problem_list"
cat jsem_problems_list | tr '\t' '+' > temp_jsem_problems_list

tags=""
  for i in `seq 2 ${#}`
  do
      if [ `echo ${2} | grep '+'` ]; then
          echo "Plus (+) is an illegal character. Exit."
          exit 1
      elif [ `echo ${2} | cut -c 1` = "-" ]; then
	  tag=`echo ${2} | cut -c 2-${#2}`
	  grep -i -v "+${tag}" temp_jsem_problems_list > temp2_jsem_problems_list
      else
	  grep -i "+${2}" temp_jsem_problems_list > temp2_jsem_problems_list
      fi
      cat temp2_jsem_problems_list > temp_jsem_problems_list
      tag_elimspace=`echo ${2} | awk '{gsub(" ", "-"); print $0;}'`
      tags="${tags}_${tag_elimspace}"
      shift
  done
cat temp_jsem_problems_list | tr '+' '\t' > temp2_jsem_problems_list
cat temp2_jsem_problems_list > temp_jsem_problems_list
rm temp2_jsem_problems_list

################################################################

# Remove the previous jsem.files
if [ -e ja_plain/jsem.files ]; then
  rm ja_plain/jsem.files
  rm ja_plain/jsem.files_??
fi

cat temp_jsem_problems_list | awk -F'\t' '{print $1}' > ja_plain/jsem.files

# Split filename entries into several files, for parallel processing:
njsem=`cat ja_plain/jsem.files | wc -l`
jsem_lines_per_split=`python -c "from math import ceil; print(int(ceil(float(${njsem})/${cores})))"`
split -l $jsem_lines_per_split ja_plain/jsem.files ja_plain/jsem.files_

# Run pipeline for each entailment problem.
for ff in ja_plain/jsem.files_??; do
  for f in `cat ${ff}`; do
    ./ja/rte_ja.sh ja_plain/$f $templates;
  done &
done

# Wait for the parallel processes to finish.
wait

# gold_dir=$1
# sys_dir=$2
 
# total=0
# correct=0
# for f in ja_results/jsem_*.answer; do
#   let total++
#   base_filename=${f##*/}
#   sys_filename=ja_plain/${base_filename}
#   gold_answer=`head -1 $f`
#   if [ ! -e ${sys_filename} ]; then
#     sys_answer="unknown"
#   else
#     sys_answer=`head -1 ${sys_filename}`
#     if [ ! "${sys_answer}" == "unknown" ] && [ ! "${sys_answer}" == "yes" ] && [ ! "${sys_answer}" == "no" ]; then
#       sys_answer="unknown"
#     fi
#   fi
#   if [ "${gold_answer}" == "${sys_answer}" ]; then
#     let correct++
#   fi
#   echo -e $f"\t"$gold_answer"\t"$sys_answer
# done

# accuracy=`echo "scale=3; $correct / $total" | bc -l`
# echo "Accuracy: "$correct" / "$total" = "$accuracy

plain_dir=ja_plain
results_dir=ja_results
# Print a summary (precision, recall, f-score) of the errors at individual problems,
# per problem category and a global score.
echo "Evaluating."
echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results of JSeM</title>
  <style>
    body {
      font-size: 1.5em;
    }
  </style>
</head>
<body>
<table border='1'>
<tr>
  <td>JSeM problem</td>
  <td>gold answer</td>
  <td>system answer</td>
  <td>proving time</td>
</tr>" > $results_dir/main_jsem.html
total_observations=0
correct_recognitions=0
attempts=0
total_proving_time=0
red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"
for system_filename in `ls -v ${results_dir}/jsem_*.answer`; do
  base_filename=${system_filename##*/} # this line obtains the filename, without the directory path.
  gold_filename=${plain_dir}/${base_filename/.txt/}
  gold_answer=`cat $gold_filename`
  system_answer=`cat $system_filename`
  time_filename=${results_dir}/${base_filename/.answer/.time}
  proving_time=`cat $time_filename`
  total_proving_time=`echo "$total_proving_time + $proving_time" | bc -l`
  total_number=$((total_number + 1))
  color=$white_color
# excluding "undef" problems
  if [ "${gold_answer}" == "undef" ]; then
    color=$gray_color
  else
    total_observations=$((total_observations + 1))
    if [ "$gold_answer" == "$system_answer" ]; then
      correct_recognitions=$((correct_recognitions + 1))
      color=$green_color
# # identifying "no system answer" with "unknown"
#     elif [ "$gold_answer" == "unknown" ] && [ "$system_answer" == "" ]; then
#       correct_recognitions=$((correct_recognitions + 1))
#       color=$green_color
    else
      color=$red_color
    fi
  fi
  echo '
<tr>
  <td><a style="background-color:'$color';" href="'${base_filename/.answer/.html}'">'${base_filename/.answer/}'</a></td>
  <td>'$gold_answer'</td>
  <td>'$system_answer'</td>
  <td>'$proving_time's</td>
</tr>' >> $results_dir/main_jsem.html
done
accuracy=`echo "scale=3; $correct_recognitions / $total_observations" | bc -l`
average_proving_time=`echo "scale=2; $total_proving_time / $total_number" | bc -l`
# average_proving_time=0
echo "
<h4><font color="red">Accuracy: "$accuracy" ("${correct_recognitions}"/"${total_observations}") </font></h4>
<h4><font color="red">Average proving time: "${average_proving_time}" </font></h4>
<h5>tags: "${tags}"</h5>
</body>
</html>
" >> $results_dir/main_jsem.html

./ja/accuracy.sh ${results_dir}/main_jsem.html > ${results_dir}/score.txt
