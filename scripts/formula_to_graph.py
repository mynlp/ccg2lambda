from __future__ import print_function
import fileinput
import subprocess
import sys

from logic_parser import lexpr
from nltk2graph import formula_to_graph

import networkx as nx

for i, line in enumerate(fileinput.input()):
    line = line.strip()
    try:
        expr = lexpr(line)
    except Exception as e:
        print('Failed to parse formula: {0}'.format(line), file=sys.stderr)
        print('Error: {0}'.format(e), file=sys.stderr)
        continue
    expr = lexpr(line)
    graph = formula_to_graph(expr)
    nx.drawing.nx_pydot.write_dot(graph, './graph_{0}.dot'.format(i))
    # nx.nx_agraph.write_dot(graph, './graph_{0}.dot'.format(i))
    process = subprocess.Popen(
        'cat ./graph_{0}.dot | dot -Tpng -o graph_{0}.png'.format(i),
        shell=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
