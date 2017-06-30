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

from ccg2lambda_tools import build_ccg_tree
from lxml import etree
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

def get_semantics_mathml(semantics):
    return "<mtext " \
           + " fontsize='" + str(kOtherSize) + "'" \
           + " color='" + kSemanticsColor + "'>" \
           + semantics \
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
        mathml_str = get_fraction_mathml(category_mathml, surf_mathml, '0')
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

def get_sentence_surface_from_tokens(ccg_tokens, attribute = 'surf'):
    return ' '.join([token.get(attribute) for token in ccg_tokens])

def convert_doc_to_mathml(doc, verbatim_strings = [], use_gold_trees=False):
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
    <meta charset='UTF-8'>
    <title>CCG to Lambda conversion</title>
    <style>
      body {
        font-size: 1em;
      }
    </style>
    <script type="text/javascript"
            src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
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
    return html_str
