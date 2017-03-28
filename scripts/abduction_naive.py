#!/usr/bin/python
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez
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

from subprocess import Popen
import subprocess

from abduction_tools import insert_axioms_in_coq_script
from knowledge import get_tokens_from_xml_node, get_lexical_relations_from_preds
from semantic_tools import is_theorem_defined

class AxiomsWordnet(object):
    """
    Create axioms using relations in WordNet.
    """
    def __init__(self):
        pass

    def attempt(self, coq_scripts, doc=None):
        return TryNaiveAbduction(coq_scripts, doc)

def TryNaiveAbduction(coq_scripts, doc):
    assert len(coq_scripts) == 2
    direct_proof_script = coq_scripts[0]
    reverse_proof_script = coq_scripts[1]

    sentences = doc.xpath('//sentence')
    assert len(sentences) == 2
    premise, conclusion = sentences
    premise_tokens = get_tokens_from_xml_node(premise)
    conclusion_tokens = get_tokens_from_xml_node(conclusion)
    axioms = set()

    for c_token in conclusion_tokens:
        p_axioms = get_lexical_relations_from_preds(premise_tokens, c_token)
        axioms.update(p_axioms)
    if not axioms:
        return 'unknown', coq_scripts

    result, new_script = run_theorem(axioms, direct_proof_script, 'yes')
    coq_scripts.append(new_script)
    if result == 'yes':
        return result, coq_scripts
    result, new_script = run_theorem(axioms, reverse_proof_script, 'no')
    coq_scripts.append(new_script)
    if result == 'no':
        return result, coq_scripts
    return 'unknown', coq_scripts
    
def run_theorem(axioms, proof_script, expected='yes'):
    augmented_script = insert_axioms_in_coq_script(axioms, proof_script)
    process = Popen(augmented_script, shell=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    output_lines = [
        line.decode('utf-8').strip() for line in process.stdout.readlines()]
    if is_theorem_defined(l.split() for l in output_lines):
        return expected, augmented_script
    else:
        return None, augmented_script

