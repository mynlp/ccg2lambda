#!/bin/bash

# This script evaluates semantic templates on the FraCaS test suite.
#
# Usage:
#  ./en/eval_fracas.sh <list of section numbers> <templates>
# 
# Example:
# ./en/eval_fracas.sh 1 2 5 6 8 9
#

# Set the name of semantic templates
templates="en/semantic_templates_en_event.yaml"

plain_dir="en_plain"
results_dir="en_results"

if [ ! -e $results_dir ]; then
  mkdir -p $results_dir
fi

# Set a coq library file
cp en/coqlib_univ.v coqlib.v
coqc coqlib.v
cp en/tactics_coq_fracas.txt tactics_coq.txt

function proving() {
  section=$1
  for f in ${plain_dir}/${section}.txt; do
    ./en/rte_en_mp_any.sh $f $templates;
  done
}

# Display the result for each problem in a html file
echo "Evaluating."
echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results of "$templates" on FraCaS </title>
  <style>
    body {
      font-size: 1.5em;
    }
  </style>
</head>
<body>
<table border='1'>
<tr>
  <td>fracas problem</td>
  <td>gold answer</td>
  <td>system answer</td>
  <td>C&C</td>
  <td>EasyCCG</td>
  <td>depccg</td>
</tr>" > $results_dir/main.html

red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"

function display() {
  section=$1
  for gold_filename in ${plain_dir}/${section}.answer; do
    base_filename=${gold_filename##*/}
    gold_answer=`cat $gold_filename`
    echo '<tr>
    <td>'${base_filename/.answer/}'</td>
    <td>'$gold_answer'</td>' >> $results_dir/main.html
    for parser in "" "candc." "easyccg." "depccg."; do 
      if [ -e ${results_dir}/${base_filename/.answer/.txt}.${parser}answer ]; then
        system_answer=`cat ${results_dir}/${base_filename/.answer/.txt}.${parser}answer`
      else
        system_answer="error"
      fi
      color=$white_color
      if [ "$gold_answer" == "yes" ] || [ "$gold_answer" == "no" ]; then
        if [ "$gold_answer" == "$system_answer" ]; then
          color=$green_color
        else
          color=$red_color
        fi
      elif [ "$system_answer" == "unknown" ] || [ "$system_answer" == "error" ] || [ "$system_answer" == "undef" ]; then
        color=$gray_color
      fi
      echo '<td><a style="background-color:'$color';" href="'${base_filename/.answer/.txt}.${parser}html'">'$system_answer'</a>' >> $results_dir/main.html
    done
    echo '</tr>' >> $results_dir/main.html
  done
}

# Collect results and print accuracies.
function calculate_score() {
  section=$1
  for f in ${plain_dir}/${section}.tok; do
    filename=${f##*/}
    base_filename=${filename/.tok/}
    num_lines=`cat $f | wc -l`
    premises="single"
    if [ "$num_lines" -gt 2 ]; then
      premises="multi"
    fi
    gold_answer=`cat ${plain_dir}/${base_filename}.answer`
    system_answer=`cat ${results_dir}/${base_filename}.txt.answer`
    candc_answer=`cat ${results_dir}/${base_filename}.txt.candc.answer`
    easyccg_answer=`cat ${results_dir}/${base_filename}.txt.easyccg.answer`
    depccg_answer=`cat ${results_dir}/${base_filename}.txt.depccg.answer`
    echo $base_filename $premises $gold_answer >> gold.results
    echo $base_filename $premises $system_answer >> system.results
    echo $base_filename $premises $candc_answer >> candc.results
    echo $base_filename $premises $easyccg_answer >> easyccg.results
    echo $base_filename $premises $depccg_answer >> depccg.results
  done
}

function evaluate() {
  section=$1
  proving $section
  display $section
  calculate_score $section
}

for section_number in $@; do
  if [ ${section_number} -eq 1 ]; then
    evaluate "fracas_*_generalized_quantifiers"
  fi
  if [ ${section_number} -eq 2 ]; then
    evaluate "fracas_*_plurals"
  fi
  if [ ${section_number} -eq 3 ]; then
    evaluate "fracas_*_nominal_anaphora"
  fi
  if [ ${section_number} -eq 4 ]; then
    evaluate "fracas_*_ellipsis"
  fi
  if [ ${section_number} -eq 5 ]; then
    evaluate "fracas_*_adjectives"
  fi
  if [ ${section_number} -eq 6 ]; then
    evaluate "fracas_*_comparatives"
  fi
  if [ ${section_number} -eq 7 ]; then
    evaluate "fracas_*_temporal_reference"
  fi
  if [ ${section_number} -eq 8 ]; then
    evaluate "fracas_*_verbs"
  fi
  if [ ${section_number} -eq 9 ]; then
    evaluate "fracas_*_attitudes"
  fi
  if [ ${section_number} -gt 9 ]; then
    echo "${section_number}: there is no such section"
  fi
done

echo "
</body>
</html>
" >> $results_dir/main.html

echo -e "Multi-parsers:" > ${results_dir}/score.txt
python en/report_results.py gold.results system.results >> ${results_dir}/score.txt
echo -e "C&C:" >> ${results_dir}/score.txt
python en/report_results.py gold.results candc.results >> ${results_dir}/score.txt
echo -e "EasyCCG:" >> ${results_dir}/score.txt
python en/report_results.py gold.results easyccg.results >> ${results_dir}/score.txt
echo -e "depccg:" >> ${results_dir}/score.txt
python en/report_results.py gold.results depccg.results >> ${results_dir}/score.txt

cat ${results_dir}/score.txt

rm -f gold.results system.results candc.results easyccg.results depccg.results


