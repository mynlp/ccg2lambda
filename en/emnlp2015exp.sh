#!/bin/bash
#
#  Copyright 2015 Pascual Martinez-Gomez
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

# This script evaluates a list of templates that assign semantics
# to nodes of CCG derivations of fracas premises and hypotheses.
# Please, use it as:
# 
# ./en/emnlp2015exp.sh <semantic_template.yaml> <dataset>
# 
# E.g.
# ./en/emnlp2015exp.sh en/semantic_templates_en_emnlp2015.yaml fracas.xml
#
# You need to have a file in the current directory named candc_location.txt
# where you have the absolute directory path to C&C parser.
# Inside the directory pointed by candc_location.txt, there should be
# a directory called "bin" that contains the binaries of C&C parser
# and another directory called "models" that contains the models.
# For example:
# $ cat candc_location.txt
#   /home/pasmargo/software/candc/candc-1.00

cp en/coqlib_fracas.v coqlib.v
coqc coqlib.v
cp en/tactics_coq_fracas.txt tactics_coq.txt

# Check that the number of arguments is correct.
if [ "$#" -ne 2 ]; then
  echo "Error: Number of arguments invalid".
  echo "Usage: ./evaluate_template.sh <semantic_template.yaml> <dataset>"
  exit 1
fi
# This variable contains the filename where the category templates are.
category_templates=$1
if [ ! -f $category_templates ]; then
  echo "Error: File with semantic templates does not exist."
  echo "Usage: ./evaluate_template.sh <semantic_template.yaml> <dataset>"
  exit 1
fi

# This variable contains the name of the dataset (fracas or jsem).
dataset=$2
if [ ! -f $dataset ]; then
  echo "Error: File with entailment problems (in XML) does not exist."
  echo "Usage: ./evaluate_template.sh <semantic_template.yaml> <dataset>"
  exit 1
fi

# Set a variable with the command to invoke the CCG parser.
parser_dir=`cat en/candc_location.txt`
parser_cmd="${parser_dir}/bin/candc \
    --models ${parser_dir}/models \
    --candc-printer xml \
    --input"

# These variables contain the names of the directories where intermediate
# results will be written.
plain_dir=${dataset}"_plain"
parsed_dir=${dataset}"_parsed"
results_dir=${dataset}"_results"

# 1) If directory or files with raw sentences do not exist, then run the python
#    script that extracts them.
#    2.1) Anotate well the files, so that we can evaluate semantic templates
#         per problem category.
#    2.2) Extract the gold entailment relation and save it into a file indexed
#         by the name of the dataset problem.
echo "Extracting problems from "${dataset}" XML file"
if [ ! -d "$plain_dir" ]; then
  mkdir -p $plain_dir
fi
python en/extract_entailment_problems.py $dataset $plain_dir
# Tokenize text.
for f in ${plain_dir}/*.txt; do
  if [ ! -e "${f/.txt/.tok}" ]; then
    cat $f | \
    perl en/tokenizer.perl -l en 2>/dev/null | \
    sed 's/ _ /_/g' > ${f/.txt/.tok}
  fi
done

# 3) If directory with parsed sentences does not exist, then call the parser.
#    Here we check whether the variable is pointing to the right C&C parser directory.
if [ ! -d "${parser_dir}" ]; then
  echo "Parser directory does not exist. Exit."
  exit 1
fi
if [ ! -e "${parser_dir}"/bin/candc ]; then
  echo "The variable parser_dir might not be pointing to the candc directory. Exit."
  exit 1
fi

# Parse files.
echo -n "Parsing ${dataset}"
if [ ! -d "$parsed_dir" ]; then
  mkdir $parsed_dir
fi
for f in ${plain_dir}/*.tok; do
  base_filename=${f##*/}
  if [ ! -e "${parsed_dir}/${base_filename}.candc.xml" ]; then
    # Display progress.
    echo -n "."
    # C&C parse and conversion into transccg format.
    eval $parser_cmd $f \
      2> ${parsed_dir}/${base_filename}.log \
       > ${parsed_dir}/${base_filename}.candc.xml
  fi
  if [ ! -e "${parsed_dir}/${base_filename/.tok/}.xml" ]; then
    python en/candc2transccg.py ${parsed_dir}/${base_filename}.candc.xml \
      > ${parsed_dir}/${base_filename/.tok/}.xml
  fi
done
echo

# 5) For every entailment problem, do semantic parsing and prove theorem. Print debug information:
#    5.1) CCG tree in HTML, with semantic assignments (for every premise and hypothesis).
#    5.2) Possible error messages when assigning semantics to each tree (the results/*.html).
#    5.3) The resulting coq program, with the exact instruction to run it in coq (verbatim in results/*.html).
#    5.4) Final entailment judgment, and its gold judgment (in results/*.answer).
echo -n "Judging entailment"
if [ ! -d $results_dir ]; then
  mkdir -p $results_dir
fi
for f in ${plain_dir}/*.tok; do
  base_filename=${f##*/}
  if [ ! -e "$parsed_dir/${base_filename/.tok/.sem.xml}" ]; then
    # Display progress.
    echo -n "."
    python scripts/semparse.py \
      $parsed_dir/${base_filename/.tok/.xml} \
      $category_templates \
      $parsed_dir/${base_filename/.tok/.sem.xml} \
      --arbi-types \
      2> $parsed_dir/${base_filename/.tok/.sem.err}
  fi
  if [ ! -e "${results_dir}/${base_filename/.tok/.answer}" ]; then
    python scripts/prove.py \
      $parsed_dir/${base_filename/.tok/.sem.xml} \
    --graph_out ${results_dir}/${base_filename/.tok/.html} \
    --abduction spsa \
    > ${results_dir}/${base_filename/.tok/.answer} \
    2> ${results_dir}/${base_filename/.tok/.err}
  fi
done
echo

# 6) Print a summary (precision, recall, f-score) of the errors at individual fracas problems,
#    per problem category and a global score.
echo "Evaluating."
echo "<!doctype html>
<html lang='en'>
<head>
  <meta charset='UTF-8'>
  <title>Evaluation results of "$category_templates"</title>
  <style>
    body {
      font-size: 2em;
    }
  </style>
</head>
<body>
<table border='1'>
<tr>
  <td>fracas problem</td>
  <td>gold answer</td>
  <td>system answer</td>
</tr>" > $results_dir/main.html
red_color="rgb(255,0,0)"
green_color="rgb(0,255,0)"
white_color="rgb(255,255,255)"
gray_color="rgb(136,136,136)"
for gold_filename in ${plain_dir}/*.answer; do
  base_filename=${gold_filename##*/}
  system_filename=${results_dir}/${base_filename/.txt/.answer}
  gold_answer=`cat $gold_filename`
  system_answer=`cat $system_filename`
  color=$white_color
  if [ "$gold_answer" == "yes" ] || [ "$gold_answer" == "no" ]; then
    if [ "$gold_answer" == "$system_answer" ]; then
      color=$green_color
    else
      color=$red_color
    fi
  elif [ "$system_answer" == "unknown" ] || [ "$system_answer" == "undef" ]; then
    color=$gray_color
  fi
  echo '
<tr>
  <td><a style="background-color:'$color';" href="'${base_filename/.answer/.html}'">'${base_filename/.answer/}'</a></td>
  <td>'$gold_answer'</td>
  <td>'$system_answer'</td>
</tr>' >> $results_dir/main.html
done
echo "
</body>
</html>
" >> $results_dir/main.html

# Collect results and print accuracies.
rm -f gold.results system.results

for f in ${plain_dir}/*.tok; do
  base_filename=${f##*/}
  base_filename=${base_filename/.tok/}
  num_lines=`cat $f | wc -l`
  premises="single"
  if [ "$num_lines" -gt 2 ]; then
    premises="multi"
  fi
  gold_answer=`cat ${plain_dir}/${base_filename}.answer`
  system_answer=`cat ${results_dir}/${base_filename}.answer`
  echo $base_filename $premises $gold_answer >> gold.results
  echo $base_filename $premises $system_answer >> system.results
done

python en/report_results.py gold.results system.results
