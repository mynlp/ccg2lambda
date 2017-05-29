import codecs
import json
import fileinput
import sys

fname=sys.argv[1]

with codecs.open(fname, 'r', 'utf-8') as fin:
    for i, line in enumerate(fin):
        problem = json.loads(line.strip())
        assert 'sentence1' in problem
        assert 'sentence2' in problem
        print(problem['sentence1'])
        print(problem['sentence2'])
