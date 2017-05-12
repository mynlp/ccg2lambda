#!/bin/bash

# This is a script to do evaluation for NLP2016.
#
# ./nlp2016exp.sh <cores> <result_dir>
#

cores=${1:-3}
results_dir=$2
mode=${3-plain}

if [ ! -d ${results_dir} ]; then
  mkdir ${results_dir}
fi

echo "------------GQ section (evaluation: ${mode})"
./ja/evaluate_jsem_parallel.sh $cores "Generalized Quantifier" entailment -presupposition
mv ja_results ${results_dir}/gq_${mode}
echo "GQ section: Done------------"

echo "------------Plural section (evaluation: ${mode})"
./ja/evaluate_jsem_parallel.sh $cores "Plural" entailment -presupposition "-nominal anaphora"
mv ja_results ${results_dir}/plural_${mode}
echo "Plural section: Done------------"

echo "------------Adjective section (evaluation: ${mode})"
./ja/evaluate_jsem_parallel.sh $cores "Adjective" entailment -presupposition
mv ja_results ${results_dir}/adjective_${mode}
echo "Adjective section: Done------------"

echo "------------Verb section (evaluation: ${mode})"
./ja/evaluate_jsem_parallel.sh $cores "Verb" entailment -presupposition
mv ja_results ${results_dir}/verb_${mode}
echo "Verb section: Done------------"

echo "------------Attitude section (evaluation: ${mode})"
./ja/evaluate_jsem_parallel.sh $cores "Attitude" entailment -presupposition
mv ja_results ${results_dir}/attitude_${mode}
echo "Attitude section: Done------------"

echo "compute Accuracy: ${mode}"
./ja/accuracy.sh ${results_dir}/gq_${mode}/main_jsem.html > ${results_dir}/gq_${mode}/score.txt
mv base_results.txt ${results_dir}/${mode}.all.results

./ja/accuracy.sh ${results_dir}/plural_${mode}/main_jsem.html > ${results_dir}/plural_${mode}/score.txt
cat base_results.txt >> ${results_dir}/${mode}.all.results

./ja/accuracy.sh ${results_dir}/adjective_${mode}/main_jsem.html > ${results_dir}/adjective_${mode}/score.txt
cat base_results.txt >> ${results_dir}/${mode}.all.results

./ja/accuracy.sh ${results_dir}/verb_${mode}/main_jsem.html > ${results_dir}/verb_${mode}/score.txt
cat base_results.txt >> ${results_dir}/${mode}.all.results

./ja/accuracy.sh ${results_dir}/attitude_${mode}/main_jsem.html > ${results_dir}/attitude_${mode}/score.txt
cat base_results.txt >> ${results_dir}/${mode}.all.results

rm base_results.txt

