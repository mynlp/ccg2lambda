#!/usr/bin/python3
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

import cgi
import re
import sys

from lxml import etree

from ccg2lambda_tools import build_ccg_tree
from knowledge import get_tokens_from_xml_node
from semantic_index import find_node_by_id

kUpwardsTree = True
kDisplaySemantics = True
kDisplayFeatures = True
kFeatureSize = 0.8
kOtherSize = 1.0
kCategoryColor = 'Red'
kFeatureColor = 'Purple'
kSemanticsColor = 'Blue'
kLexicalColor = 'Black'
kEntityColor = 'Green'
kPosColor = 'Green'
# The full list of colors is:
# Black Green Silver Lime Gray Olive White Maroon Red Purple Fuchsia Yellow Navy
# Blue Teal Aqua

def get_fraction_mathml(numerator, denominator, line_thickness = 3,
                   rule = '', upwards = kUpwardsTree):
    if upwards:
        numerator, denominator = denominator, numerator
    mathml_str = "<mfrac linethickness='" + str(line_thickness) + "px'>\n" \
               + "  <mrow>" + numerator + "</mrow>\n" \
               + "  <mrow>" + denominator + "</mrow>\n" \
               + "</mfrac>\n"
    if rule:
        mathml_str = "<mrow><mo>" + cgi.escape(rule) + "</mo>" + mathml_str + "</mrow>"
    return mathml_str

def get_category_mathml(category):
    cats_feats = re.findall(r'([\w\\/()]+)(\[.+?\])*', category)
    mathml_str = ''
    for cat, feat in cats_feats:
        cat_mathml =  "  <mi mathvariant='italic'" \
                           + " fontsize='" + str(kOtherSize) + "'" \
                           + " color='" + kCategoryColor + "'>" \
                           + cat \
                      + "  </mi>\n"
        if feat != '' and kDisplayFeatures:
            mathml_str += "<msub>\n" \
                        + cat_mathml \
                        + "  <mrow>\n" \
                        + "    <mi mathvariant='italic'" \
                             + " fontsize='" + str(kFeatureSize) + "'" \
                             + " color='" + kFeatureColor + "'>" \
                             + feat \
                        + "  </mi>\n" \
                        + "  </mrow>\n" \
                        + "</msub>\n"
        else:
            mathml_str += cat_mathml
    return mathml_str

def get_surface_mathml(surface):
    return "<mtext " \
           + " fontsize='" + str(kOtherSize) + "'" \
           + " color='" + kLexicalColor + "'>" \
           + surface \
           + "</mtext>\n"

def get_entity_mathml(entity):
    return "<mtext " \
           + " fontsize='" + str(kOtherSize) + "'" \
           + " color='" + kEntityColor + "'>" \
           + entity \
           + "</mtext>\n"

def get_pos_mathml(pos):
    return "<mtext " \
           + " fontsize='" + str(kOtherSize) + "'" \
           + " color='" + kPosColor + "'>" \
           + pos \
           + "</mtext>\n"

def get_semantics_mathml(semantics):
    return "<mtext " \
           + " fontsize='" + str(kOtherSize) + "'" \
           + " color='" + kSemanticsColor + "'>" \
           + cgi.escape(semantics) \
           + "</mtext>\n"

def convert_node_to_mathml(ccg_node, sem_tree, tokens):
    mathml_str = ''
    category = ccg_node.get('category').strip()
    category_mathml = get_category_mathml(category)
    if len(ccg_node) == 0:
        token_id = ccg_node.get('terminal')
        token = find_node_by_id(token_id, tokens)
        surf = token.get('surf')
        surf_mathml = get_surface_mathml(surf)
        pos = token.get('pos')
        pos_mathml = get_pos_mathml(pos)
        entity = token.get('entity')
        if not entity == None:
            entity_mathml = get_entity_mathml(entity)
            pos_mathml = pos_mathml + "<mtext>,</mtext><mspace width='.1em'/>" + entity_mathml
        pos1 = token.get('pos1')
        if not (pos1 == None or pos1 == '*'):
            pos1_mathml = get_pos_mathml(pos1)
            pos_mathml = pos_mathml + "<mspace width='.1em'/>" + pos1_mathml
        pos2 = token.get('pos2')
        if not (pos2 == None or pos2 == '*'):
            pos2_mathml = get_pos_mathml(pos2)
            pos_mathml = pos_mathml + "<mspace width='.1em'/>" + pos2_mathml
        pos3 = token.get('pos3')
        if not (pos3 == None or pos3 == '*'):
            pos3_mathml = get_pos_mathml(pos3)
            pos_mathml = pos_mathml + "<mspace width='.1em'/>" + pos3_mathml
        if pos == '.':
            mathml_str = get_fraction_mathml(category_mathml, surf_mathml, '0')
        else:
            mathml_pos_str = get_fraction_mathml(category_mathml, pos_mathml, '0')
            mathml_str = get_fraction_mathml(mathml_pos_str, surf_mathml, '0')
    elif len(ccg_node) == 1:
        mathml_str_child = convert_node_to_mathml(ccg_node[0], sem_tree, tokens)
        rule = ccg_node.get('rule')
        mathml_str = get_fraction_mathml(category_mathml, mathml_str_child, '3', rule)
    elif len(ccg_node) > 0:
        mathml_str_children = ''
        for child in ccg_node:
            mathml_str_child = convert_node_to_mathml(child, sem_tree, tokens)
            mathml_str_children += mathml_str_child
        rule = ccg_node.get('rule')
        mathml_str = get_fraction_mathml(category_mathml, mathml_str_children, '3', rule)
    if sem_tree is not None and kDisplaySemantics:
        span_id = ccg_node.get('id')
        sem_node = find_node_by_id(span_id, sem_tree)
        semantics = sem_node.get('sem')
        semantics_mathml = get_semantics_mathml(semantics)
        mathml_str = get_fraction_mathml(semantics_mathml, mathml_str, '0')
    return mathml_str

def get_surf_from_xml_node(node):
    tokens = node.xpath(
        "./tokens/token[not(@surf='*')]/@surf | ./tokens/token[@surf='*']/@base")
    return ' '.join(tokens)

def convert_doc_to_mathml(doc, use_gold_trees=False):
    """
    This function expects an XML <document>, which is then converted
    into a presentation MathML string.
    """
    num_sentences = int(doc.xpath('count(./sentences/sentence)'))
    mathml_str = ""
    for sent_ind, sentence in enumerate(doc.xpath('./sentences/sentence')):
        gold_tree_index = int(sentence.get('gold_tree', -1))
        if sent_ind < num_sentences - 1:
            sentence_label = 'Premise {0}'.format(sent_ind)
        else:
            sentence_label = 'Conclusion'
        sentence_text = get_surf_from_xml_node(sentence)
        ccg_trees = sentence.xpath('./ccg')
        sem_trees = sentence.xpath('./semantics')
        tokens = sentence.xpath('./tokens')
        if not tokens:
            return mathml_str
        tokens = tokens[0]
        assert len(ccg_trees) >= len(sem_trees)
        for i in range(len(ccg_trees)):
            ccg_tree_id = ccg_trees[i].get('id', str(i))
            try:
                ccg_tree = build_ccg_tree(ccg_trees[i])
            except ValueError:
                mathml_str += "<p>{0}, tree {1}: {2}</p>\n".format(
                                sentence_label, ccg_tree_id, sentence_text) \
                            + "<p>Syntactic parse error. Visualization skipped.</p>"
                continue
            if gold_tree_index == i:
                ccg_tree_id += " (gold)"
            sem_tree = None if i >= len(sem_trees) else sem_trees[i]
            if sem_tree is not None:
                sem_tree = build_ccg_tree(sem_tree)
            mathml_str += "<p>{0}, tree {1}: {2}</p>\n".format(
                            sentence_label, ccg_tree_id, sentence_text) \
                        + "<math xmlns='http://www.w3.org/1998/Math/MathML'>\n" \
                        + convert_node_to_mathml(ccg_tree, sem_tree, tokens) \
                        + "</math>\n"
    verbatim_strings = doc.xpath('./proof/master_theorem/theorems/theorem/coq_script/text()')
    verbatim_text = ""
    if verbatim_strings:
       verbatim_text = "<p>Script piped to coq</p>"
       for vb_str in verbatim_strings:
           verbatim_text += "<pre>\n" + vb_str + "\n</pre>\n"
    doc_mathml_str = '{0}\n{1}'.format(mathml_str, verbatim_text)
    return doc_mathml_str

def wrap_mathml_in_html(mathml_str):
    html_str = """\
    <!DOCTYPE html>
    <html lang='en'>
    <head>
      <meta charset='UTF-8'/>
      <title>CCG to Lambda conversion</title>
      <style>
        body {
          font-size: 1em;
        }
      </style>
      <script type="text/javascript"
              src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
      </script>
    </head>
    <body>
    """
    html_str += mathml_str
    html_str += """\
    </body>
    </html>
    """
    return html_str

def convert_root_to_mathml(root, use_gold_trees=False):
    """
    This function expects an XML root. Then, it converts each document doc
    into a presentation MathML string, and wraps them with HTML code.
    """
    doc_mathml_strs = []
    for doc_ind, doc in enumerate(root.xpath('./document')):
        doc_id = doc.get('id', doc_ind)
        doc_mathml_str = convert_doc_to_mathml(doc, use_gold_trees)
        doc_mathml_strs.append(doc_mathml_str)
    html_str = wrap_mathml_in_html('\n'.join([s for s in doc_mathml_strs]))
    return html_str

# TODO: possibly deprecated. Confirm and then remove this function.
def convert_doc_to_mathml_(doc, verbatim_strings = [], use_gold_trees=False):
    """
    This function expects a list of ccg_trees, and a list of tokens
    (as produced by transccg). Then, it converts each pair (ccg_tree, ccg_tokens)
    into a presentation MathML string, and wraps them with HTML code.
    verbatim_strings contains a list of strings that should be printed
    verbatim at the end of the HTML document, for debugging.
    """
    ccg_trees = []
    if use_gold_trees:
        for sentence in doc.xpath('./sentences/sentence'):
            gold_tree_index = int(sentence.get('gold_tree', '0'))
            ccg_trees.append(sentence.xpath('./ccg')[gold_tree_index])
        ccg_trees = [build_ccg_tree(c) for c in ccg_trees]
    else:
        ccg_trees = [build_ccg_tree(c) for c in doc.xpath('./sentences/sentence/ccg[1]')]
    sem_trees = [build_ccg_tree(c) for c in doc.xpath('./sentences/sentence/semantics')]
    if not sem_trees:
        sem_trees = [None] * len(ccg_trees)
    tokens = doc.xpath('./sentences/sentence/tokens')
    assert len(ccg_trees) == len(tokens) 
    num_hypotheses = len(ccg_trees) - 1
    sentence_ids = ["Premise {0}: ".format(i + 1) for i in range(num_hypotheses)]
    sentence_ids.append("Conclusion: ")
    mathml_str = ""
    for i in range(len(ccg_trees)):
        sentence_surface = ' '.join(tokens[i].xpath('token/@surf'))
        mathml_str += "<p>" + sentence_ids[i] + sentence_surface + "</p>\n" \
                    + "<math xmlns='http://www.w3.org/1998/Math/MathML'>" \
                    + convert_node_to_mathml(ccg_trees[i], sem_trees[i], tokens[i]) \
                    + "</math>"

    verbatim_text = ""
    if verbatim_strings:
       verbatim_text = "<p>Script piped to coq</p>"
       for vb_str in verbatim_strings:
           verbatim_text += "<pre>\n" + vb_str + "\n</pre>\n"

    html_str = """\
  <!doctype html>
  <html lang='en'>
  <head>
    <style>
      body {
        font-size: 1em;
      }
    </style>
    <meta charset='UTF-8'>
    <title>CCG to Lambda conversion</title>
    <script type="text/javascript"
            src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
    </script>
  </head>
  <body>
  """
    html_str += mathml_str
    html_str += verbatim_text
    html_str += """\
  </body>
  </html>
  """
    return cgi.escape(html_str)
