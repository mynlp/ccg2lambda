# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez and Hitomi Yanaka
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

import codecs
import logging
import re
import subprocess

from knowledge import get_lexical_relations
from nltk2coq import normalize_interpretation
from semantic_types import get_dynamic_library_from_doc
from tactics import get_tactics
from abduction_tools import find_final_subgoal_line_index, find_final_conclusion_sep_line_index, try_sim_abductions, try_reduce_subgoals
from subprocess import call, Popen
from nltk.corpus import wordnet as wn
from collections import *
import urllib.parse
import unicodedata

def build_knowledge_axioms(doc):
    if not doc:
        return ''
    axioms = get_lexical_relations(doc)
    axioms_str = ""
    for axiom in axioms:
        axioms_str += axiom + '\n'
        axiom_name = axiom.split()[1]
        axioms_str += 'Hint Resolve {0}.\n'.format(axiom_name)
    axioms_str += '\n'
    return axioms_str

def get_formulas_from_doc(doc):
    """
    Returns string representations of logical formulas,
    as stored in the "sem" attribute of the root node
    of semantic trees.
    If a premise has no semantic representation, it is ignored.
    If there are no semantic representation at all, or the conclusion
    has no semantic representation, it returns None to signal an error.
    """
    formulas = [s.get('sem', None) for s in doc.xpath('//sentence/semantics/span[1]')]
    if len(formulas) < 2 or formulas[-1] == None:
        return None
    formulas = [f for f in formulas if f is not None]
    return formulas

def prove_doc(doc, abduction=None, similarity=None):
    """
    Retrieve from trees the logical formulas and the types
    (dynamic library).
    Then build a prover script and retrieve entailment judgement.
    If results are not conclusive, attempt basic abduction.
    """
    coq_scripts = []
    coq_scripts2 = []
    formulas = get_formulas_from_doc(doc)
    if not formulas:
        return 'unknown', coq_scripts
    dynamic_library_str, formulas = get_dynamic_library_from_doc(doc, formulas)

    premises, conclusion = formulas[:-1], formulas[-1]

    if similarity:
        inference_result_int1, inference_result_int2, axioms1, axioms2 = 0, 0, 0, 0
        word_similarity1, subgoals_similarity1, word_similarity2, subgoals_similarity2 = 0, 0, 0, 0
        origin_subgoals_similarity1, origin_subgoals_similarity2 = 0, 0
        steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1 = 0, 0, 0, 0, 0, 0, 0, 0
        steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2 = 0, 0, 0, 0, 0, 0, 0, 0
        subj_subgoals1, acc_subgoals1, dat_subgoals1, subj_subgoals2, acc_subgoals2, dat_subgoals2 = 0, 0, 0, 0, 0, 0 

        ## prove A->B
        inference_result, coq_script = \
        prove_statements(premises, conclusion, dynamic_library_str)
        coq_scripts.append(coq_script)
        if inference_result:
            inference_result_int1 = 1
            axioms1, word_similarity1, subgoals_similarity1, origin_subgoals_similarity1, steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1, subj_subgoals1, acc_subgoals1, dat_subgoals1 = calculate_similarity(coq_scripts, dynamic_library_str)
            word_similarity1, subgoals_similarity1, origin_subgoals_similarity1 = 1, 1, 1
        else:
            negated_conclusion = negate_conclusion(conclusion)
            inference_result, coq_script = \
            prove_statements(premises, negated_conclusion, dynamic_library_str)
            coq_scripts.append(coq_script)
            if inference_result:
                inference_result_int1 = 0.5
                axioms1, word_similarity1, subgoals_similarity1, origin_subgoals_similarity1, steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1, subj_subgoals1, acc_subgoals1, dat_subgoals1 = calculate_similarity(coq_scripts, dynamic_library_str)
                word_similarity1, subgoals_similarity1, origin_subgoals_similarity1 = 1, 1, 1
            else:
                ## try abductions
                inference_result_str, abduction_scripts = try_sim_abductions(coq_scripts)
                coq_scripts.extend(abduction_scripts)
                if inference_result_str == 'yes':
                    inference_result_int1 = 1
                    axioms1, word_similarity1, subgoals_similarity1, origin_subgoals_similarity1, steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1, subj_subgoals1, acc_subgoals1, dat_subgoals1 = calculate_similarity(coq_scripts, dynamic_library_str)
                elif inference_result_str == 'no':
                    inference_result_int1 = 0.5
                    axioms1, word_similarity1, subgoals_similarity1, origin_subgoals_similarity1, steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1, subj_subgoals1, acc_subgoals1, dat_subgoals1 = calculate_similarity(coq_scripts, dynamic_library_str)
                else:
                    ## reduce subgoals
                    inference_result_str, new_abduction_scripts = try_reduce_subgoals(coq_scripts)
                    coq_scripts.extend(new_abduction_scripts)
                    if inference_result_str == 'yes':
                        axioms1, word_similarity1, subgoals_similarity1, origin_subgoals_similarity1, steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1, subj_subgoals1, acc_subgoals1, dat_subgoals1 = calculate_similarity(coq_scripts, dynamic_library_str)
                    #elif inference_result_str == 'coq_error':
                    else:
                        return inference_result_str, coq_scripts
        ## prove B->A
        inference_result, coq_script = \
        prove_statements([conclusion], premises[0], dynamic_library_str)
        coq_scripts.append(coq_script)
        coq_scripts2.append(coq_script)
        if inference_result:
            inference_result_int2 = 1
            axioms2, word_similarity2, subgoals_similarity2, origin_subgoals_similarity2, steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2, subj_subgoals2, acc_subgoals2, dat_subgoals2 = calculate_similarity(coq_scripts2, dynamic_library_str)
            word_similarity2, subgoals_similarity2, origin_subgoals_similarity2 = 1, 1, 1
        else:
            negated_conclusion = negate_conclusion(conclusion)
            inference_result, coq_script = \
            prove_statements(premises, negated_conclusion, dynamic_library_str)
            coq_scripts.append(coq_script)
            coq_scripts2.append(coq_script)
            if inference_result:
                #contradiction is mostly similar
                inference_result_int2 = 0.5
                axioms2, word_similarity2, subgoals_similarity2, origin_subgoals_similarity2, steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2, subj_subgoals2, acc_subgoals2, dat_subgoals2 = calculate_similarity(coq_scripts2, dynamic_library_str)
                word_similarity2, subgoals_similarity2, origin_subgoals_similarity2 = 1, 1, 1
            else:
                ## try abductions
                inference_result_str, abduction_scripts = try_sim_abductions(coq_scripts2)
                coq_scripts.extend(abduction_scripts)
                coq_scripts2.extend(abduction_scripts)
                if inference_result_str == 'yes':
                    inference_result_int2 = 1
                    axioms2, word_similarity2, subgoals_similarity2, origin_subgoals_similarity2, steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2, subj_subgoals2, acc_subgoals2, dat_subgoals2 = calculate_similarity(coq_scripts2, dynamic_library_str)
                elif inference_result_str == 'no':
                    inference_result_int2 = 0.5
                    axioms2, word_similarity2, subgoals_similarity2, origin_subgoals_similarity2, steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2, subj_subgoals2, acc_subgoals2, dat_subgoals2 = calculate_similarity(coq_scripts2, dynamic_library_str)
                else:
                    ## reduce subgoals
                    inference_result_str, new_abduction_scripts = try_reduce_subgoals(coq_scripts2)
                    coq_scripts.extend(new_abduction_scripts)
                    coq_scripts2.extend(new_abduction_scripts)
                    if inference_result_str == 'yes':
                        axioms2, word_similarity2, subgoals_similarity2, origin_subgoals_similarity2, steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2, subj_subgoals2, acc_subgoals2, dat_subgoals2 = calculate_similarity(coq_scripts2, dynamic_library_str)
                    else:
                        return inference_result_str, coq_scripts
        return [inference_result_int1, word_similarity1, axioms1, subgoals_similarity1,\
        inference_result_int2, word_similarity2, axioms2, subgoals_similarity2,\
        origin_subgoals_similarity1, origin_subgoals_similarity2,\
        steps1, ex_ind1, and_ind1, eq_ind1, ex_intro1, conj1, fun1, fun_ind1,\
        steps2, ex_ind2, and_ind2, eq_ind2, ex_intro2, conj2, fun2, fun_ind2,\
        subj_subgoals1, acc_subgoals1, dat_subgoals1, subj_subgoals2, acc_subgoals2, dat_subgoals2\
        ], coq_scripts

    else:    
        inference_result, coq_script = \
            prove_statements(premises, conclusion, dynamic_library_str)
        coq_scripts.append(coq_script)
        if inference_result:
            inference_result_str = 'yes'
        else:
            negated_conclusion = negate_conclusion(conclusion)
            inference_result, coq_script = \
            prove_statements(premises, negated_conclusion, dynamic_library_str)
            coq_scripts.append(coq_script)
            if inference_result:
                inference_result_str = 'no'
            else:
                inference_result_str = 'unknown'
        if abduction and inference_result_str == 'unknown':
            inference_result_str, abduction_scripts = \
                abduction.attempt(coq_scripts, doc)
            coq_scripts.extend(abduction_scripts)
        return inference_result_str, coq_scripts

# Check whether the string "is defined" appears in the output of coq.
# In that case, we return True. Otherwise, we return False.
def is_theorem_defined(output_lines):
    for output_line in output_lines:
        if len(output_line) > 2 and 'is defined' in (' '.join(output_line[-2:])):
            return True
    return False

def resolve_prefix_to_infix_operations(expr_str, pred = 'R', symbol = '', brackets = ['', '']):
    cat_expr_str = expr_str
    i = 0
    while (pred + '(') in cat_expr_str:
        cat_expr_str = \
          re.sub(pred + r'\(([^' + pred + r']+?),([^' + pred + r']+?)\)',
                 brackets[0] + r'\1' + symbol + r'\2' + brackets[1], cat_expr_str)
        i += 1
        if i > 100:
            logging.warning('There is probably a problem in the resolution of ' \
                    'concatenation expressions in {0}'.format(expr_str))
    return cat_expr_str

def substitute_invalid_chars(script, replacement_filename):
    with codecs.open(replacement_filename, 'r', 'utf-8') as finput:
        repl = dict(line.strip().split() for line in finput)
        for invalid_char, valid_char in repl.items():
            script = script.replace(invalid_char, valid_char)
    return script

# This function receives two arguments. The first one is a list of the logical
# interpretations of the premises (only one interpretation per premise).
# The second argument is a string with a single interpretation of the conclusion.
def prove_statements(premises, conclusion, dynamic_library = ''):
    # Transform these interpretations into coq format:
    #   interpretation1 -> interpretation2 -> ... -> conclusion
    interpretations = premises + [conclusion]
    interpretations = [normalize_interpretation(interp) for interp in interpretations]
    coq_formulae = ' -> '.join(interpretations)
    # Input these formulae to coq and retrieve the results.
    tactics = get_tactics()
    input_coq_script = ('echo \"Require Export coqlib.\n'
        '{0}\nTheorem t1: {1}. {2}.\" | coqtop').format(
        dynamic_library, coq_formulae, tactics)
    input_coq_script = substitute_invalid_chars(input_coq_script, 'replacement.txt')
    process = subprocess.Popen(\
      input_coq_script, \
      shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output_lines = [str(line).strip().split() for line in process.stdout.readlines()]
    return is_theorem_defined(output_lines), input_coq_script

# Given a string reprsenting the logical interpretation of the conclusion,
# it returns a string with the negated conclusion.
def negate_conclusion(conclusion):
    return - conclusion

def wordnet_similarity(word1, word2):
    word_similarity_list = []
    wordFromList1 = wn.synsets(word1)
    wordFromList2 = wn.synsets(word2)
    for w1 in wordFromList1:
        for w2 in wordFromList2:
            if w1.path_similarity(w2) is not None: 
                word_similarity_list.append(w1.path_similarity(w2))
    if(word_similarity_list):
        word_similarity = max(word_similarity_list)
    else:
        # cannot path similarity but somehow similar
        word_similarity = 0.5
    return word_similarity

def calculate_similarity(coq_scripts, dynamic_library_str):
    # extract axioms from coq_scripts and calculate axiom similarity
    word1 = ""
    word2 = ""
    word_similarity = 0
    originsubgoals = 0
    deletesubgoals = 0
    originsubgoals2 = 0
    deletesubgoals2 = 0
    axioms = 0
    origin_coq_scripts = ""
    # count steps and inference_rules
    steps = 0
    subgoal_flg = 0
    subgoals = []
    assertnums = 0
    admit_command1 = ""
    admit_command2 = ""
    ex_ind, and_ind, eq_ind, conj, ex_intro, fun, fun_ind = 0, 0, 0, 0, 0, 0, 0
    # arguments' case of subgoals
    subj_subgoals, acc_subgoals, dat_subgoals = 0, 0, 0
    merge_axioms = defaultdict(list)

    # use last coq_scripts
    coq_lines = coq_scripts[-1].split("\n")
    for coq_line in coq_lines:
      if re.search("Hint", coq_line):
        if re.search("approx", coq_line):
          #word2vec
          word_lines = coq_line.split("_")
          word1 = word_lines[2]
          if re.search("(.*)\.", word_lines[3]):
            word2 = word_lines[3].rstrip(".")
          else:
            word2 = word_lines[3]
          merge_axioms[word1].append("w2v "+word2)
        elif re.search("ax_copy", coq_line) or re.search("ax_remove", coq_line) or re.search("ax_phrase", coq_line):
           #phrase level = calculate similarity as 1
           continue
        else:
          #wordnet  
          word_lines = coq_line.split("_")
          word1 = word_lines[2]
          word2 = re.search("(.*)\.", word_lines[3]).group(1)
          merge_axioms[word1].append("wn "+word2)

    for pr, ax in merge_axioms.items():
      pre_similarities = []
      for a in ax:
        dic = a.split()[0]
        word = a.split()[1]
        if dic == "w2v":
          if unicodedata.category(pr[0]) == "Lo":
            #if Japanese, do URL encode
            pr = urllib.parse.quote(pr)
            word = urllib.parse.quote(word)
          process = Popen(\
            'curl http://localhost:5000/word2vec/similarity?w1='+ pr +'\&w2='+ word, \
            shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
          pre_similarity = process.communicate()[0]
          pre_similarities.append(float(pre_similarity.decode()))
        elif dic == "wn":
          pre_similarity = wordnet_similarity(pr, word)
          pre_similarities.append(pre_similarity)
      word_similarity += max(pre_similarities)
      axioms += 1

    if axioms > 0:
      word_similarity = word_similarity/axioms

    new_coq_scripts = coq_scripts[-1].replace(
      'nltac. Set Firstorder Depth 3. nltac',
      'nltac. Set Firstorder Depth 3. repeat nltac_base.')
    process = Popen(\
      new_coq_scripts, \
      shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output_lines = [line.decode('utf-8').strip() for line in process.stdout.readlines()]
    for o in output_lines:
      # add "focused" for new Coq's script
      if re.search('^[0-9]* focused subgoals?$', o):
        deletesubgoals = int(re.search(r'^([0-9]*) focused subgoals?$', o).group(1))
        break
      if re.search('^[0-9]* subgoals?$', o):
        deletesubgoals = int(re.search(r'^([0-9]*) subgoals?$', o).group(1))
        break
    line_index_last_conclusion_sep = find_final_conclusion_sep_line_index(output_lines)
    line_index_subgoal_sep = find_final_subgoal_line_index(output_lines)

    for line in output_lines[line_index_subgoal_sep:line_index_last_conclusion_sep]:
      # only count Hxx and not count 'True'
      if re.search(r'^[H]', line) and not 'True' in line:
        originsubgoals = originsubgoals + 1

    if originsubgoals != 0:
      subgoals_similarity = (originsubgoals-deletesubgoals)/originsubgoals
    else:
      ## no subgoals
      subgoals_similarity = 1
    ## to do: detect why sometimes subgoals_similarity < 0   
    if subgoals_similarity < 0:
      subgoals_similarity = 0
    #count steps and inference rules
    if subgoals_similarity != 1:
      #add admit
      for line in output_lines[line_index_last_conclusion_sep:]:
        #accumulate subgoals
        if subgoal_flg == 1:
          subgoals.append(line)
          subgoal_flg = 0
        #check subgoal_flg
        if re.search("============================",line) or re.search("subgoal [0-9]* is:", line):
          subgoal_flg = 1
      for s in subgoals:
        #check the subgoals' case
        if "(Subj" in s:
          subj_subgoals += 1
        elif "(Acc" in s:
          acc_subgoals += 1
        elif "(Dat" in s:
          dat_subgoals += 1 
        #create admit command
        if "?" in s:
          # substitute existential variables to normal variables(?123 -> x123)
          s = re.sub("\?", "x", s)
          assertnums += 1
          words = s.split()
          admit_command1 += " assert("
          for w in words:
            if re.search("^[xyz][0-9]*", w):
              var = re.search("^([xyz][0-9]*)", w).group(1)
              admit_command1 += "forall "+var+", "
          admit_command1 += s+"). admit."
        else:
          admit_command2 += " admit."
      count_coq_scripts = coq_scripts[-1].replace(
        ' repeat nltac_base. Qed.',
        admit_command1+' repeat nltac_base.'+admit_command2+' Grab Existential Variables. admit. admit. Qed. Print t1.')
      subj_subgoals = subj_subgoals/len(subgoals)
      acc_subgoals = acc_subgoals/len(subgoals)
      dat_subgoals = dat_subgoals/len(subgoals)
    else:
       count_coq_scripts = coq_scripts[-1].replace(
       'Qed.', 'Qed. Print t1.')

    process = Popen(\
      count_coq_scripts, \
      shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output_lines = [line.decode('utf-8').strip() for line in process.stdout.readlines()]
    #count steps and inference_rules
    for (i, o) in enumerate(output_lines):
      if re.search("ex_ind", o):
        ex_ind += o.count("ex_ind")
        steps += o.count("ex_ind") 
      if re.search("and_ind", o):
        and_ind += o.count("and_ind")
        steps += o.count("and_ind") 
      if re.search("eq_ind", o):
        eq_ind += o.count("eq_ind")
        steps += o.count("eq_ind") 
      if re.search("eq_intro", o):
        ex_intro += o.count("ex_intro")
        steps += o.count("ex_intro") 
      if re.search("conj", o):
        conj += o.count("conj")
        steps += o.count("conj")
      #if re.search("^\(?fun", o):
      #  fun += 1
      #  steps += 2
    fun = axioms + assertnums + 1
    fun_ind = fun
    steps = steps + fun + fun_ind

    ## extract origin subgoals from coq_scripts and calculate subgoal similarity
    if len(coq_scripts) == 1 or len(coq_scripts) == 3 or len(coq_scripts) == 5:
      origin_coq_scripts = coq_scripts[0].replace(
        'nltac. Set Firstorder Depth 3. nltac',
        'nltac. Set Firstorder Depth 3. repeat nltac_base')
    #negation
    if len(coq_scripts) == 2 or len(coq_scripts) == 4:
      origin_coq_scripts = coq_scripts[1].replace(
        'nltac. Set Firstorder Depth 3. nltac',
        'nltac. Set Firstorder Depth 3. repeat nltac_base')
    process = Popen(\
      origin_coq_scripts, \
      shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output_lines = [line.decode('utf-8').strip() for line in process.stdout.readlines()]
    for o in output_lines:
      # add "focused" for new Coq's script
      if re.search('^[0-9]* focused subgoals?$', o):
        deletesubgoals2 = int(re.search(r'^([0-9]*) focused subgoals?$', o).group(1))
        break
      if re.search('^[0-9]* subgoals?$', o):
        deletesubgoals2 = int(re.search(r'^([0-9]*) subgoals?$', o).group(1))
        break
    line_index_last_conclusion_sep2 = find_final_conclusion_sep_line_index(output_lines)
    line_index_subgoal_sep2 = find_final_subgoal_line_index(output_lines)
    for line in output_lines[line_index_subgoal_sep2:line_index_last_conclusion_sep2]:
      ## only count Hxx and not count 'True'
      if re.search(r'^[H]', line) and not 'True' in line:
        originsubgoals2 = originsubgoals2 + 1
    if originsubgoals2 != 0:
      origin_subgoals_similarity = (originsubgoals2-deletesubgoals2)/originsubgoals2
    else:
      ## no subgoals
      origin_subgoals_similarity = 1
    ## to do: detect why sometimes subgoals_similarity < 0   
    if origin_subgoals_similarity < 0:
      origin_subgoals_similarity = 0


    return axioms, word_similarity, subgoals_similarity, origin_subgoals_similarity, \
    steps, ex_ind, and_ind, eq_ind, ex_intro, conj, fun, fun_ind, \
    subj_subgoals, acc_subgoals, dat_subgoals


