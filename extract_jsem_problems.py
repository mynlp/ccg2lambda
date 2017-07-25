# Create a list of jsem-problems with tags for entailment-type and phenomena-type ("jsem_problems_list").
# "jsem_problems_list" is needed to run evaluate_jsem_tags.sh

import codecs
from copy import deepcopy
from lxml import etree
import os
import re
import sys

# Read the FraCaS or JSeM xml file into a tree and return it.
def ReadFracasFile(fracas_filename):
  finput = open(fracas_filename, 'r')
  tree_string = finput.read()
  finput.close()
  tree = etree.fromstring(tree_string)
  return tree

# The text T of a T-H pair may contain several premises splitted into
# several "<p ...> ... </p>" leaves. This function retrieves them
# and returns them as a list of premises.
# In FraCaS, the text is attached directly between <p ...> "text" </p> tags,
# while in JSeM, it is found under <p ...> <script> "text in Japanese" </script> </p>
def GetPremisesFromNode_(node):
  text_and_idx = []
  for i, child in enumerate(node):
    if child.tag == 'p':
      text = child.text.strip() if not child.get('script', None) \
                                else child.get('script').text.strip()
      idx  = int(child.attrib['idx'])
      text_and_idx.append((text, idx))
  text_and_idx.sort(key = lambda x: x[1])
  premises = [x[0] for x in text_and_idx]
  return premises

def GetTextFromScriptNode(script):
  if len(script) > 0:
    # There is a comment node inside of script.
    text = script[0].tail.strip()
  else:
    text = script.text.strip()
  return text

def GetTextFromNode(node):
  script = node.findall('.//script')
  if not script:
    text = node.text.strip()
  else:
    text = GetTextFromScriptNode(script[0])
  return text

def GetPremisesFromNode(node):
  text_and_idx = []
  premise_nodes = node.findall('.//p')
  for premise_node in premise_nodes:
    text = GetTextFromNode(premise_node)
    idx  = int(premise_node.attrib['idx'])
    text_and_idx.append((text, idx))
  text_and_idx.sort(key = lambda x: x[1])
  premises = [x[0] for x in text_and_idx]
  return premises

# Retrieve the Hypothesis side of an entailment pair.
def GetHypothesisFromNode(node):
  for child in node:
    if child.tag == 'h':
      text = GetTextFromNode(child)
      return text
  return ''

def NormalizeSectionName(section_name):
  # Remove parenthesis and non alphabetic characters.
  section_name = re.sub(r'[^a-zA-Z ]', '', section_name)
  # Strip whitespaces from beginning or end of string.
  section_name = section_name.strip()
  # Replace whitespaces by underscore and lowercase.
  section_name = re.sub(r' ', '_', section_name).lower()
  return section_name

def EscapeReservedChars(sentence):
  sentence_escaped = sentence
  sentence_escaped = re.sub(r'-', r'_', sentence_escaped)
  return sentence_escaped

def GetFracasProblems(contents):
  problems = []
  current_section = 'nosection'
  for node in contents:
    if node.tag == 'comment' \
       and 'class' in node.attrib \
       and node.attrib['class'] == 'section':
      current_section = NormalizeSectionName(node.text)
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
        current_section = NormalizeSectionName(node.attrib['phenomena'].split(',')[0])
        phenomena = node.attrib['phenomena'].split(', ') # comma and space
      if 'inference_type' in node.attrib:
        inference_type = node.attrib['inference_type'].split(', ') # comma and space
      premises = GetPremisesFromNode(node)
      hypothesis = GetHypothesisFromNode(node)
      sentences = premises + [hypothesis]
      sentences = [EscapeReservedChars(s) for s in sentences]
      problem = FracasProblem(problem_id, current_section, sentences, answer, phenomena, inference_type)
      problems.append(problem)
  return problems

class FracasProblem:
  def __init__(self, problem_id, section_name, sentences, answer, phenomena, inference_type):
    self.problem_id = problem_id
    self.section_name = section_name
    self.sentences = sentences
    self.answer = answer
    self.phenomena = phenomena # list of phenomenon
    self.inference_type = inference_type # list of inference_type

def WriteFracasProblems(problems, fracas_dirname, file_prefix = ''):
  foutput_list = codecs.open("jsem_problems_list", 'w', 'utf-8')
  for i, problem in enumerate(problems):
    tags = "" # initialize tags (string)
    n_sentence = 0 # initialize sentences counter
    # Write sentences.
    if problem.problem_id == 'unknown':
      continue
    problem_filename = '{0}/{1}{2:03d}_{3}.txt'.format(fracas_dirname,
                                                       file_prefix,
                                                       int(problem.problem_id),
                                                       problem.section_name)
    problem_filename2 = '{0}{1:03d}_{2}.txt'.format(file_prefix,
                                                       int(problem.problem_id),
                                                       problem.section_name)
    foutput = codecs.open(problem_filename, 'w', 'utf-8')
    for sentence in problem.sentences:
      foutput.write(u'{0}\n'.format(sentence))
      n_sentence += 1 # count the number of sentences
    foutput.close()
    # Add entry in "jsem_problems_list"
    tags = tags + '\t' + problem.answer
    for type in problem.inference_type:
 #     if not type:
 #       tags = tags + type
 #     else:
      tags = tags + '\t' + type
    for phenomenon in problem.phenomena:
 #     if not tags:
 #       tags = tags + phenomenon
 #     else:
      tags = tags + '\t' + phenomenon
    n_premise = n_sentence - 1 # number of premises
    # add tag "single" or "multi" (premises)
    if n_premise == 1:
      tags = tags + '\t' + "single"
    else:
      tags = tags + '\t' + "multi"
    foutput_list.write('{0}{1}\n'.format(problem_filename2, tags))
    # Write the answer.
    answer_filename = '{0}/{1}{2:03d}_{3}.answer'.format(fracas_dirname,
                                                         file_prefix,
                                                         int(problem.problem_id),
                                                         problem.section_name)
    foutput = codecs.open(answer_filename, 'w', 'utf-8')
    foutput.write('{0}'.format(problem.answer))
    foutput.close()
  foutput_list.close()
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
  problems = GetFracasProblems(xml_tree)
  WriteFracasProblems(problems, output_dirname, kFilePrefix)

if __name__ == '__main__':
  main()

