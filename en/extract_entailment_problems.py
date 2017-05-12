#!/usr/bin/python
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

import codecs
from lxml import etree
import os
import re
import sys

# Read the FraCaS or JSeM xml file into a tree and return it.
def read_fracas_file(fracas_filename):
    finput = open(fracas_filename, 'r')
    tree_string = finput.read()
    finput.close()
    tree = etree.fromstring(tree_string)
    return tree

def get_text_from_script_Node(script):
    if len(script) > 0:
        # There is a comment node inside of script.
        text = script[0].tail.strip()
    else:
        text = script.text.strip()
    return text

def get_text_from_node(node):
    script = node.findall('.//script')
    if not script:
        text = node.text.strip()
    else:
        text = get_text_from_script_Node(script[0])
    return text

def get_premises_from_node(node):
    """
    The text T of a T-H pair may contain several premises splitted into
    several "<p ...> ... </p>" leaves. This function retrieves them
    and returns them as a list of premises.
    In FraCaS, the text is attached directly between <p ...> "text" </p> tags,
    while in JSeM, it is found under <p ...> <script> "text in Japanese" </script> </p>
    """
    text_and_idx = []
    premise_nodes = node.findall('.//p')
    for premise_node in premise_nodes:
        text = get_text_from_node(premise_node)
        idx  = int(premise_node.attrib['idx'])
        text_and_idx.append((text, idx))
    text_and_idx.sort(key = lambda x: x[1])
    premises = [x[0] for x in text_and_idx]
    return premises

# Retrieve the Hypothesis side of an entailment pair.
def get_hypothesis_from_node(node):
    for child in node:
        if child.tag == 'h':
            text = get_text_from_node(child)
            return text
    return ''

def normalize_section_name(section_name):
    # Remove parenthesis and non alphabetic characters.
    section_name = re.sub(r'[^a-zA-Z ]', '', section_name)
    # Strip whitespaces from beginning or end of string.
    section_name = section_name.strip()
    # Replace whitespaces by underscore and lowercase.
    section_name = re.sub(r' ', '_', section_name).lower()
    return section_name

def escape_reserved_chars(sentence):
    sentence_escaped = sentence
    sentence_escaped = re.sub(r'-', r'_', sentence_escaped)
    return sentence_escaped

def get_fracas_problems(contents):
    problems = []
    current_section = 'nosection'
    for node in contents:
        if node.tag == 'comment' \
           and 'class' in node.attrib \
           and node.attrib['class'] == 'section':
            current_section = normalize_section_name(node.text)
        if node.tag == 'problem':
            # Retrieve the first answer (there should be only one).
            answer = [value for key, value in node.attrib.items() if 'answer' in key]
            assert len(answer) <= 1, 'Multiple gold entailment answers found'
            answer = None if not answer else answer[0]
            # Retrieve problem ID.
            problem_id = [value for key, value in node.attrib.items() if key.endswith('id')]
            assert len(problem_id) == 1, 'Problem has no ID'
            problem_id = problem_id[0]
            # Retrieve section name from phenomena, if any.
            if 'phenomena' in node.attrib:
                current_section = normalize_section_name(node.attrib['phenomena'].split(',')[0])
            premises = get_premises_from_node(node)
            hypothesis = get_hypothesis_from_node(node)
            sentences = premises + [hypothesis]
            # sentences = [escape_reserved_chars(s) for s in sentences]
            problem = FracasProblem(problem_id, current_section, sentences, answer)
            problems.append(problem)
    return problems

class FracasProblem(object):
    def __init__(self, problem_id, section_name, sentences, answer):
        self.problem_id = problem_id
        self.section_name = section_name
        self.sentences = sentences
        self.answer = answer

def write_fracas_problems(problems, fracas_dirname, file_prefix = ''):
    for i, problem in enumerate(problems):
        # Write sentences.
        if problem.problem_id == 'unknown':
            continue
        problem_filename = '{0}/{1}{2:03d}_{3}.txt'.format(fracas_dirname,
                                                           file_prefix,
                                                           int(problem.problem_id),
                                                           problem.section_name)
        foutput = codecs.open(problem_filename, 'w', 'utf-8')
        for sentence in problem.sentences:
            foutput.write('{0}\n'.format(sentence))
        foutput.close()
        # Write the answer.
        answer_filename = '{0}/{1}{2:03d}_{3}.answer'.format(fracas_dirname,
                                                             file_prefix,
                                                             int(problem.problem_id),
                                                             problem.section_name)
        foutput = codecs.open(answer_filename, 'w', 'utf-8')
        foutput.write('{0}'.format(problem.answer))
        foutput.close()
    return

def main(args = None):
    import textwrap
    USAGE=textwrap.dedent("""\
        Usage:
            python extract_entailment_problems.py <fracas.xml|jsem.xml> <output_directory>

            Extracts from the fracas or jsem XML file all the entailment problems. Problems are
            written separatedly in different files inside of <output_directory>.
            Each file contains one premise in every line, and the conclusion
            in the last line.
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
    if not os.path.exists(args[1]):
        print('Directory does not exist: {0}'.format(args[1]))
        sys.exit(1)
    problems_filename = args[0]
    output_dirname = args[1]
    kFilePrefix = problems_filename.split('.')[0] + '_'

    xml_tree = etree.parse(problems_filename).getroot()
    problems = get_fracas_problems(xml_tree)
    write_fracas_problems(problems, output_dirname, kFilePrefix)

if __name__ == '__main__':
    main()
