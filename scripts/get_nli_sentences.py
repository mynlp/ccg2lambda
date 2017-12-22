import codecs
import json
import fileinput
import string
import sys

from nltk import Tree

fname=sys.argv[1]

def print_tokenized_sentences(problem):
    print_tokenized_sentence(problem, 'sentence1')
    print_tokenized_sentence(problem, 'sentence2')

def print_tokenized_sentence(problem, sent_prefix):
    toks = []
    try:
        tree = Tree.fromstring(problem[sent_prefix + '_parse'])
        toks = tree.leaves()
    except ValueError:
        sentence = problem.get(sent_prefix, None)
        if sentence is None:
            toks = []
        else:
          toks = sentence.split()
    if len(toks) > 0 and toks[-1] not in string.punctuation:
        toks.append('.')
    print(' '.join(toks).replace('#', '_POUND_'))

with codecs.open(fname, 'r', 'utf-8') as fin:
    for i, line in enumerate(fin):
        problem = json.loads(line.strip())
        print_tokenized_sentences(problem)

