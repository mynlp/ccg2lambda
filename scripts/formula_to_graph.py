from __future__ import print_function
import fileinput
import logging
import subprocess
import sys

from logic_parser import lexpr
from nltk2graph import formula_to_graph

import networkx as nx

logging.basicConfig(level=logging.INFO)

for i, line in enumerate(fileinput.input()):
    line = line.strip()
    try:
        expr = lexpr(line)
    except Exception as e:
        print('Failed to parse formula: {0}'.format(line), file=sys.stderr)
        print('Error: {0}'.format(e), file=sys.stderr)
        continue
    expr = lexpr(line)
    graph = formula_to_graph(expr, normalize=True)
    graph_basename = 'graph_' + str(i)
    nx.drawing.nx_pydot.write_dot(graph, './{0}.dot'.format(graph_basename))
    process = subprocess.Popen(
        'cat ./{0}.dot | dot -Tpng -o {0}.png'.format(graph_basename),
        shell=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    logging.info('{0}.png : {1}'.format(graph_basename, expr))

