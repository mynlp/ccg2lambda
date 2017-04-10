#!/bin/bash

#calculating the total accuracy, recall and precision, and creating the confusion matrix

input=$1

cat $input | \
  sed 's/^$/#/g' | \
  tr '\n' ' ' | \
  tr '#' '\n' | \
  sed 's/</ /g' | \
  sed 's/>/ /g' | \
  grep href | \
  awk '{print $6" "$10" "$13}' \
  > base_results.txt

total_number_with_undef=`cat base_results.txt | wc -l`
total_number=`cat base_results.txt | grep -v undef | wc -l`
noanswer=`cat base_results.txt | grep -v undef | awk '$3 == "/td"' | wc -l`
correct_parsing=`cat base_results.txt | grep -v undef | awk '$3 != "/td"' | wc -l`
# counting timeout cases as "unknown"
correct_answer=`cat base_results.txt | awk '$2 == $3 || ($2 == "unknown" && $3 == "/td") || ($2 == "unknown" && $3 == "error")' | wc -l`
# correct_answer=`cat base_results.txt | awk '$2 == $3' | wc -l`

# counting the score for each gold_system pair

yes_yes=`cat base_results.txt | awk '$2 == "yes" && $3 == "yes"' | wc -l`
yes_no=`cat base_results.txt | awk '$2 == "yes" && $3 == "no"' | wc -l`
yes_unk=`cat base_results.txt | awk '$2 == "yes" && $3 == "unknown"' | wc -l`
yes_error=`cat base_results.txt | awk '$2 == "yes" && ($3 == "/td" || $3 == "error")' | wc -l`
yes_gold_total=`cat base_results.txt | awk '$2 == "yes"' | wc -l`
yes_system_total=`cat base_results.txt | grep -v undef | awk '$3 == "yes"' | wc -l`

no_yes=`cat base_results.txt | awk '$2 == "no" && $3 == "yes"' | wc -l`
no_no=`cat base_results.txt | awk '$2 == "no" && $3 == "no"' | wc -l`
no_unk=`cat base_results.txt | awk '$2 == "no" && $3 == "unknown"' | wc -l`
no_error=`cat base_results.txt | awk '$2 == "no" && ($3 == "/td" || $3 == "error")' | wc -l`
no_gold_total=`cat base_results.txt | awk '$2 == "no"' | wc -l`
no_system_total=`cat base_results.txt | grep -v undef | awk '$3 == "no"' | wc -l`

unk_yes=`cat base_results.txt | awk '$2 == "unknown" && $3 == "yes"' | wc -l`
unk_no=`cat base_results.txt | awk '$2 == "unknown" && $3 == "no"' | wc -l`
unk_unk=`cat base_results.txt | awk '$2 == "unknown" && $3 == "unknown"' | wc -l`
unk_error=`cat base_results.txt | awk '$2 == "unknown" && ($3 == "/td" || $3 == "error")' | wc -l`
unk_gold_total=`cat base_results.txt | awk '$2 == "unknown"' | wc -l`
unk_system_total=`cat base_results.txt | grep -v undef | awk '$3 == "unknown"' | wc -l`

system_correct_answer=$((yes_yes + no_no))
system_yes_no=$((yes_system_total + no_system_total))
gold_yes_no=$((yes_gold_total + no_gold_total))

noerror=`echo "scale=4; $correct_parsing / $total_number" | bc -l`
accuracy=`echo "scale=4; $correct_answer / $total_number" | bc -l`
recall=`echo "scale=4; $system_correct_answer / $gold_yes_no" | bc -l`
precision=`echo "scale=4; $system_correct_answer / $system_yes_no" | bc -l`
fone=`echo "scale=4; 2 * (($precision * $recall) / ($precision + $recall))" | bc -l`

printf "Correct parsing: %.4f (%d/%d)\n" ${noerror} $correct_parsing $total_number
printf "Accuracy: %.4f (%d/%d)\n" ${accuracy} $correct_answer $total_number
printf "Recall: %.4f\n" ${recall}
printf "Precision: %.4f\n" ${precision}
printf "F1 score: %.4f\n" ${fone}
printf "Gold_correct_total: %d\n" ${gold_yes_no}
printf "System_answer_total: %d\n" ${system_yes_no}
printf "System_correct_total: %d\n" ${system_correct_answer}
printf "\b----------------------------------------------------------------\n"
printf "                            system                              \n"
printf "     |        |     yes |      no | unknown |   error |   total \n"
printf "\b----------------------------------------------------------------\n"
printf "     |     yes| %7d | %7d | %7d | %7d | %7d \n" $yes_yes $yes_no $yes_unk $yes_error $yes_gold_total
printf "gold |      no| %7d | %7d | %7d | %7d | %7d \n" $no_yes $no_no $no_unk $no_error $no_gold_total
printf "     | unknown| %7d | %7d | %7d | %7d | %7d \n" $unk_yes $unk_no $unk_unk $unk_error $unk_gold_total
printf "     |   total| %7d | %7d | %7d | %7d | %7d \n" $yes_system_total $no_system_total $unk_system_total $noanswer $total_number
printf "\b----------------------------------------------------------------\n"

