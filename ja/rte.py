
from __future__ import print_function, unicode_literals
from lxml import etree
from depccg import PyJaAStarParser
import argparse

def depccg2xml(tree, sid):
    def traverse(node, spid=0):
        id = "s{}_sp{}".format(sid, spid)
        xml_node = etree.SubElement(res, "span")
        xml_node.set("category", str(node.cat))
        xml_node.set("begin", str(node.start_of_span))
        xml_node.set("end", str(node.start_of_span+len(node)))
        xml_node.set("id", id)
        if node.is_leaf:
            xml_node.set("terminal",
                    "s{}_{}".format(sid, node.head_id))
        else:
            spid, childid = traverse(node.left_child, spid+1)
            if not node.is_unary:
                spid, tmp = traverse(node.right_child, spid+1)
                childid += " " + tmp
            xml_node.set("child", childid)
            xml_node.set("rule", node.op_string)
        return spid, id
    res = etree.Element("ccg")
    res.set("id", "s{}_ccg0".format(sid))
    _, id = traverse(tree)
    res.set("root", str(id))
    return res


parser = argparse.ArgumentParser("A* CCG parser")
parser.add_argument("model", help="model directory")
parser.add_argument("input", help="input xml")
args = parser.parse_args()

xml_root = etree.parse(args.input).getroot()
sents = xml_root[0][0]

parser = PyJaAStarParser(args.model)
res = parser.parse_doc(
        [[t.get("surf") for t in sent[0]] for sent in sents])

for i, (sent, tree) in enumerate(zip(sents, res)):
    sent.append(depccg2xml(tree, i))

print(etree.tostring(xml_root,
    pretty_print=True).decode("utf-8"))
