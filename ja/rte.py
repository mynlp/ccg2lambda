
from __future__ import print_function, unicode_literals
from lxml import etree
from depccg import PyJaAStarParser, PyAStarParser
import argparse

Parsers = {"en": PyAStarParser, "ja": PyJaAStarParser}

class depccg2xml(object):
    def __init__(self, sid):
        self.sid       = sid
        self._spid     = 0
        self.processed = 0

    @property
    def spid(self):
        self._spid += 1
        return self._spid

    def process(self, tree, score=None):
        def traverse(node):
            id = "s{}_sp{}".format(self.sid, self.spid)
            xml_node = etree.SubElement(res, "span")
            xml_node.set("category", str(node.cat.multi_valued))
            xml_node.set("begin", str(node.start_of_span))
            xml_node.set("end", str(node.start_of_span+len(node)))
            xml_node.set("id", id)
            if node.is_leaf:
                xml_node.set("terminal",
                        "s{}_{}".format(self.sid, node.head_id))
            else:
                childid = traverse(node.left_child)
                if not node.is_unary:
                    tmp = traverse(node.right_child)
                    childid += " " + tmp
                xml_node.set("child", childid)
                xml_node.set("rule", node.op_string)
            return id

        res = etree.Element("ccg")
        res.set("id", "s{}_ccg{}".format(self.sid, self.processed))
        id = traverse(tree)
        res.set("root", str(id))
        if score is not None:
            res.set("score", str(score))
        self.processed += 1
        return res


parser = argparse.ArgumentParser("A* CCG parser")
parser.add_argument("model", help="model directory")
parser.add_argument("lang", help="language", choices=Parsers.keys())
parser.add_argument("input", help="input xml")
parser.add_argument("--nbest", default=1, type=int, help="output nbest parses")
args = parser.parse_args()

xml_root = etree.parse(args.input).getroot()
sents = xml_root[0][0]

parser = Parsers[args.lang](args.model, nbest=args.nbest, loglevel=3)
res = parser.parse_doc(
        [[t.get("surf") for t in sent[0]] for sent in sents])

for i, (sent, parsed) in enumerate(zip(sents, res)):
    runner = depccg2xml(i)
    for tree, score in parsed:
        sent.append(runner.process(tree, score))

print(etree.tostring(xml_root, pretty_print=True).decode("utf-8"))
