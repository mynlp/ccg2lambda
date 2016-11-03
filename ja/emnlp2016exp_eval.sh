#!/bin/bash

results_dir=$1
mode=$2

sections="gq plural adjective verb attitude"

speed () {
  grep 'Average' ${results_dir}/$1/main_jsem.html | awk '{print $5}'
}
accuracy () {
  grep 'Accuracy' ${results_dir}/$1/score.txt | awk '{print $2}'
}
recall () {
  grep 'Recall' ${results_dir}/$1/score.txt | awk '{print $2}'
}
precision () {
  grep 'Precision' ${results_dir}/$1/score.txt | awk '{print $2}'
}
gcorrect () {
  grep 'Gold_correct_total' ${results_dir}/$1/score.txt | awk '{print $2}'
}
sysanswer () {
  grep 'System_answer_total' ${results_dir}/$1/score.txt | awk '{print $2}'
}
syscorrect () {
  grep 'System_correct_total' ${results_dir}/$1/score.txt | awk '{print $2}'
}
correct () {
  grep 'Accuracy' ${results_dir}/$1/score.txt | sed 's@[)(/]@ @g' | awk '{print $3}'
}
total () {
  grep 'Accuracy' ${results_dir}/$1/score.txt | sed 's@[)(/]@ @g' | awk '{print $4}'
}

total_plain=0
total_syscorrect=0
total_gcorrect=0
total_correct=0 # TODO: what is the difference between syscorrect and correct?
total_sysanswer=0
total_avspeed=0
printf " ----------------------------------------------------------\n" \
  > ${results_dir}/${mode}.results.table
printf "%9s |   count| accuracy| recall| precision| av.speed| \n" ${mode} \
  >> ${results_dir}/${mode}.results.table
printf " ----------------------------------------------------------\n" \
  >> ${results_dir}/${mode}.results.table
for section in ${sections}; do
  speed_plain=`speed "${section}_${mode}"`
  accuracy_plain=`accuracy "${section}_${mode}"`
  recall_plain=`recall "${section}_${mode}"`
  precision_plain=`precision "${section}_${mode}"`
  gcorrect=`gcorrect "${section}_${mode}"`
  sysanswer=`sysanswer "${section}_${mode}"`
  syscorrect=`syscorrect "${section}_${mode}"`
  correct_plain=`correct "${section}_${mode}"`
  num_plain=`total "${section}_${mode}"`
  let total_plain=($total_plain + $num_plain)
  let total_syscorrect=($total_syscorrect + $syscorrect)
  let total_gcorrect=($total_gcorrect + $gcorrect)
  let total_correct=($total_correct + $correct_plain)
  let total_sysanswer=($total_sysanswer + $sysanswer)
  total_avspeed=`echo "scale=2; ($total_avspeed + ($speed_plain * $num_plain))" | bc -l`
  printf "%9s | %6d | %7s | %5s | %8s | %7s |\n" \
    $section $num_plain $accuracy_plain $recall_plain $precision_plain $speed_plain
done >> ${results_dir}/${mode}.results.table

total_accuracy=`echo "scale=4; ($total_correct / $total_plain)" | bc -l`
total_recall=`echo "scale=4; ($total_syscorrect / $total_gcorrect)" | bc -l`
total_precision=`echo "scale=4; ($total_syscorrect / $total_sysanswer)" | bc -l`
total_avspeed=`echo "scale=2; ($total_avspeed / $total_plain)" | bc -l`
printf "    Total | %6d | %7s | %5s | %8s | %7s |\n" \
  $total_plain ${total_accuracy} ${total_recall} ${total_precision} ${total_avspeed} \
  >> ${results_dir}/${mode}.results.table

