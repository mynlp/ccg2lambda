#!/usr/bin/python
# -*- coding: utf-8 -*-

from subprocess import Popen
import subprocess

from abduction_tools import InsertAxiomsInCoqScript
from knowledge import get_tokens_from_xml_node, GetLexicalRelationsFromPreds
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
        p_axioms = GetLexicalRelationsFromPreds(premise_tokens, c_token)
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
    augmented_script = InsertAxiomsInCoqScript(axioms, proof_script)
    process = Popen(augmented_script, shell=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    output_lines = [
        line.decode('utf-8').strip() for line in process.stdout.readlines()]
    if is_theorem_defined(l.split() for l in output_lines):
        return expected, augmented_script
    else:
        return None, augmented_script

