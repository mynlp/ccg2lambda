#!/usr/bin/python3
# -*- coding: utf-8 -*-
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

import os
import re
import sys

def get_fracas_info(problem_id):
    """
    Given a problem ID, e.g. fracas_001_generalized_quantifiers,
    it returns the fracas number "001" and the section name
    "generalized_quantifiers".
    """
    info = re.findall(r'fracas_(\d\d\d)_(.+)', problem_id)
    assert info, 'Correct Fracas ID information could not be retrieved for {0}' \
      .format(problem_id)
    fracas_num, section = info[0]
    return int(fracas_num), section

def load_answers(finput_filename):
    finput = open(finput_filename, 'r')
    answers = {}
    for line in finput:
        line_splitted = line.strip().split()
        assert len(line_splitted) >= 2, \
          'Line should have more than 1 field: {0}'.format(line)
        problem_id = line_splitted[0] # E.g. fracas_001_quantifiers
        premises = line_splitted[1] # Either "single" or "multi"
        answer = line_splitted[2] if len(line_splitted) > 2 else 'unknown'
        fracas_num, section = get_fracas_info(problem_id)
        answers[fracas_num] = {}
        answers[fracas_num]['answer'] = answer
        answers[fracas_num]['section'] = section
        answers[fracas_num]['premises'] = premises
    finput.close()
    return answers

def accumulate(d, section, premises):
    if section not in d:
        d[section] = {'single' : 0.0,
                      'multi'  : 0.0}
    d[section][premises] += 1
    d['total'][premises] += 1

def compare_answers(gold_answers, system_answers, sections):
    """
    Compute accuracy of system's answers by section and by
    number of premises (single vs. multiple).
    """
    # Collect total and hits counters.
    total = {'total' : {'single' : 0.0, 'multi' : 0.0}}
    hits  = {'total' : {'single' : 0.0, 'multi' : 0.0}}
    for fracas_num in gold_answers:
        gold_data = gold_answers[fracas_num]
        if fracas_num not in system_answers:
            continue
        system_data = system_answers[fracas_num]
        assert gold_data['section'] == system_data['section'] \
               and gold_data['premises'] == system_data['premises'], \
          'Fracas problem inconsistent: {0} vs {1}'.format(gold_data, system_data)
        if gold_data['section'] not in sections:
            continue
        section = gold_data['section']
        premises = gold_data['premises']
        if gold_data['answer'] == 'undef':
            continue
        accumulate(total, section, premises)
        if gold_data['answer'] == system_data['answer']:
            accumulate(hits, section, premises)
    return hits, total

def set_default_counts(system_accuracies, section_names):
    for section_name in section_names:
        if section_name not in system_accuracies:
            system_accuracies[section_name] = {'single' : 0.0, 'multi' : 0.0}
        if 'single' not in system_accuracies[section_name]:
            system_accuracies[section_name]['single'] = 0.0
        if 'multi' not in system_accuracies[section_name]:
            system_accuracies[section_name]['multi'] = 0.0

def print_plain_accuracies(system_accuracies, section_names):
    print(' ' * 30 + 'all premi.' + ' ' * 10 + 'single' + ' ' * 11 + 'multi')
    system_hits, system_total = system_accuracies
    set_default_counts(system_hits, section_names)
    set_default_counts(system_total, section_names)

    for section in section_names:
        row = '{0: <25} | '.format(section)
        # All premises:
        if system_total[section]['single'] + system_total[section]['multi'] > 0:
            row += '     {0:.2f}     '\
                .format((system_hits[section]['single'] + system_hits[section]['multi']) \
                        / (system_total[section]['single'] + system_total[section]['multi']))
        else:
            row += '     ----     '
        row += ' | '
        # Single premises:
        if system_total[section]['single'] > 0:
            row += '     {0:.2f}     '.format((system_hits[section]['single']) \
                                              / (system_total[section]['single']))
        else:
            row += '     ----     '
        row += ' | '
        # Multiple premises:
        if system_total[section]['multi'] > 0:
            row += '     {0:.2f}     '.format((system_hits[section]['multi']) \
                               / (system_total[section]['multi']))
        else:
            row += '     ----     '
        print(row)

def main(args = None):
    import textwrap
    USAGE=textwrap.dedent("""\
        Usage:
            python report_results.py <gold.results> <system.results>

            It reports nicely the results of RTE in fracas. Files in parameters
            contain one line per fracas problem, such as:
            <fracas_problem_id> <single|multi> <answer>

                 all premi.   single     multi
   gen. quant.      .5      |   .5    |   .5
   plurals          .5      |   .5    |   .5
   adjectives       .5      |   .5    |   .5
   comparatives     .5      |   .5    |   .5
   attitudes        .5      |   .5    |   .5
      """)
    if args is None:
        args = sys.argv[1:]
    if len(args) != 2:
        print('Wrong number of arguments.')
        print(USAGE)
        sys.exit(1)
    if not os.path.exists(args[0]):
        print('File does not exist: {0}'.format(args[0]))
        sys.exit(1)
    gold_filename = args[0]
    if not os.path.exists(args[1]):
        print('File does not exist: {0}'.format(args[1]))
        sys.exit(1)
    system_filename = args[1]

    gold_answers = load_answers(gold_filename)
    system_answers = load_answers(system_filename)

    section_names = ['generalized_quantifiers',
                     'plurals',
                     'adjectives',
                     'comparatives',
                     'attitudes',
                     'verbs',
                     'total']

    system_accuracies = compare_answers(gold_answers, system_answers, section_names)
    print_plain_accuracies(system_accuracies, section_names)

if __name__ == '__main__':
    main()
