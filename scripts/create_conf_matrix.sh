#!/bin/bash

#calculating the total accuracy, recall and precision, and creating the confusion matrix
#
# ./create_conf_matrix.sh <gold.results | plain.results>
#

input=$1

total_number_with_undef=`cat ${input} | wc -l`
total_number=`cat ${input} | grep -v undef | wc -l`
noanswer=`cat ${input} | grep -v undef | awk '$3 == "/td"' | wc -l`
correct_parsing=`cat ${input} | grep -v undef | awk '$3 != "/td"' | wc -l`
# counting timeout cases as "unknown"
correct_answer=`cat ${input} | awk '$2 == $3 || ($2 == "unknown" && $3 == "/td")' | wc -l`
# correct_answer=`cat ${input} | awk '$2 == $3' | wc -l`

# counting the score for each gold_system pair

yes_yes=`cat ${input} | awk '$2 == "yes" && $3 == "yes"' | wc -l`
yes_no=`cat ${input} | awk '$2 == "yes" && $3 == "no"' | wc -l`
yes_unk=`cat ${input} | awk '$2 == "yes" && $3 == "unknown"' | wc -l`
yes_error=`cat ${input} | awk '$2 == "yes" && $3 == "/td"' | wc -l`
yes_gold_total=`cat ${input} | awk '$2 == "yes"' | wc -l`
yes_system_total=`cat ${input} | grep -v undef | awk '$3 == "yes"' | wc -l`

no_yes=`cat ${input} | awk '$2 == "no" && $3 == "yes"' | wc -l`
no_no=`cat ${input} | awk '$2 == "no" && $3 == "no"' | wc -l`
no_unk=`cat ${input} | awk '$2 == "no" && $3 == "unknown"' | wc -l`
no_error=`cat ${input} | awk '$2 == "no" && $3 == "/td"' | wc -l`
no_gold_total=`cat ${input} | awk '$2 == "no"' | wc -l`
no_system_total=`cat ${input} | grep -v undef | awk '$3 == "no"' | wc -l`

unk_yes=`cat ${input} | awk '$2 == "unknown" && $3 == "yes"' | wc -l`
unk_no=`cat ${input} | awk '$2 == "unknown" && $3 == "no"' | wc -l`
unk_unk=`cat ${input} | awk '$2 == "unknown" && $3 == "unknown"' | wc -l`
unk_error=`cat ${input} | awk '$2 == "unknown" && $3 == "/td"' | wc -l`
unk_gold_total=`cat ${input} | awk '$2 == "unknown"' | wc -l`
unk_system_total=`cat ${input} | grep -v undef | awk '$3 == "unknown"' | wc -l`

system_correct_answer=$((yes_yes + no_no))
system_yes_no=$((yes_system_total + no_system_total))
gold_yes_no=$((yes_gold_total + no_gold_total))

noerror=`echo "scale=4; $correct_parsing / $total_number" | bc -l`
accuracy=`echo "scale=4; $correct_answer / $total_number" | bc -l`
recall=`echo "scale=4; $system_correct_answer / $gold_yes_no" | bc -l`
precision=`echo "scale=4; $system_correct_answer / $system_yes_no" | bc -l`
fone=`echo "scale=4; 2 * (($precision * $recall) / ($precision + $recall))" | bc -l`

echo -e "Accuracy: "${accuracy}" ("$correct_answer"/"$total_number")\n"\
"Recall: ${recall}\n"\
"Precision: ${precision}\n"\
"F1 score: ${fone}\n"\
"---------------------------------------------------------\n"\
"                            system                              \n"\
"     |        |      yes|       no|  unknown|    total\n"\
"---------------------------------------------------------\n"\
"     |     yes| $yes_yes| $yes_no| $yes_unk| $yes_gold_total\n"\
"gold |      no| $no_yes| $no_no| $no_unk| $no_gold_total\n"\
"     | unknown| $unk_yes| $unk_no| $unk_unk| $unk_gold_total\n"\
"     |   total| $yes_system_total| $no_system_total| $unk_system_total| $total_number\n"\
"---------------------------------------------------------"


# echo -e "Correct parsing: "${noerror}" ("$correct_parsing"/"$total_number")\n"\
# "Accuracy: "${accuracy}" ("$correct_answer"/"$total_number")\n"\
# "Recall: ${recall}\n"\
# "Precision: ${precision}\n"\
# "F1 score: ${fone}\n"\
# "Gold_correct_total: ${gold_yes_no}\n"\
# "System_answer_total: ${system_yes_no}\n"\
# "System_correct_total: ${system_correct_answer}\n"\
# "----------------------------------------------------------------\n"\
# "                            system                              \n"\
# "     |        |      yes|       no|  unknown|    error|    total\n"\
# "----------------------------------------------------------------\n"\
# "     |     yes| $yes_yes| $yes_no| $yes_unk| $yes_error| $yes_gold_total\n"\
# "gold |      no| $no_yes| $no_no| $no_unk| $no_error| $no_gold_total\n"\
# "     | unknown| $unk_yes| $unk_no| $unk_unk| $unk_error| $unk_gold_total\n"\
# "     |   total| $yes_system_total| $no_system_total| $unk_system_total| $noanswer| $total_number\n"\
# "----------------------------------------------------------------"








