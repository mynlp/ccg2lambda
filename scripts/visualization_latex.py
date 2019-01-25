#!/usr/bin/python3
# -*- coding: utf-8 -*-

import cgi
import re

from ccg2lambda_tools import build_ccg_tree
from lxml import etree
from semantic_index import find_node_by_id

kUpwardsTree = True
kDisplaySemantics = True
kDisplayFeatures = True

def get_fraction_latex(numerator, denominator, rule = '', upwards = kUpwardsTree):
    if upwards:
        numerator, denominator = denominator, numerator
    latex_str = "\infer{" + numerator + "}" \
               + "{" + denominator + "}"
    if rule:
        numerator, denominator = denominator, numerator
    label = cgi.escape(rule)
    normalized = label.replace('&lt;B1','\\FC') \
                      .replace('&gt;B1','\\BC') \
                      .replace('&lt;','\\FA') \
                      .replace('&gt;','\\BA') \
                      .replace('fa','\\FA') \
                      .replace('ba','\\BA') \
                      .replace('ba','\\BA') \
                      .replace('&','')
    latex_str = "\n\infer[" + normalized + "]{" + numerator + "}" \
               + "{" + denominator + "}"
    return latex_str

def get_lex_latex(numerator, denominator, rule = '', upwards = kUpwardsTree):
    if upwards:
        numerator, denominator = denominator, numerator
    latex_str = "\infer{" + numerator + "}" \
               + "{" + denominator + "}"
    if rule:
        numerator, denominator = denominator, numerator
    latex_str = "\n\infer{" + numerator + "}" \
               + "{" + denominator + "}"
    return latex_str

def get_sem_latex(numerator, denominator, rule = '', upwards = kUpwardsTree):
    if upwards:
        numerator, denominator = denominator, numerator
    latex_str = "\deduce{" + numerator + "}" \
               + "{" + denominator + "}"
    if rule:
        numerator, denominator = denominator, numerator
    latex_str = "\deduce{" +  numerator + "}{" + denominator + "}" 
    latex_str = "\n\deduce{\\SR{" + numerator + "}}{" + denominator + "}"
    # latex_str = "\deduce{\\begin{tabular}{c}$" + numerator + "$\\end{tabular}}" \
    #            + "{" + denominator + "}"
    return latex_str

def get_category_latex(category):
    cats_feats = re.findall(r'([\w\\/()]+)(\[.+?\])*', category)
    latex_str = ''
    for cat, feat in cats_feats:
        cat_latex =  cat.replace('\\','\\backslash ')
        if feat != '' and kDisplayFeatures:
            normalized = feat.replace('=true','') \
                             .replace('mod=','') \
                             .replace('case=','') \
                             .replace('fin=','') \
                             .replace('form=','')
            latex_str += cat_latex + normalized
        else:
            latex_str += cat_latex
    return latex_str

def get_surface_latex(surface):
    return "\mbox{" + surface + "}"

def get_pos_latex(pos):
    return "\mathrm{" + pos + "}"

def get_semantics_latex(semantics):
    normalized = semantics.replace('\\','\\lambda ') \
                          .replace('&','$\\\\$\\,\\wedge\\,') \
                          .replace('|','\\vee') \
                          .replace('->','\\to') \
                          .replace('all ','\\forall ') \
                          .replace('exists ','\\exists ') \
                          .replace(' TrueP','\\top') \
                          .replace(' True','\\top') \
                          .replace('-','\\neg ') \
                          .replace('_','')
    return normalized

def convert_node_to_latex(ccg_node, sem_tree, tokens):
    latex_str = ''
    category = ccg_node.get('category').strip()
    category_latex = get_category_latex(category)
    if len(ccg_node) == 0:
        token_id = ccg_node.get('terminal')
        token = find_node_by_id(token_id, tokens)
        surf = token.get('surf')
        surf_latex = get_surface_latex(surf)
        if surf == '.':
            latex_str = '.'
        else:
            latex_str = get_lex_latex(surf_latex, category_latex)
    elif len(ccg_node) == 1:
        latex_str_child = convert_node_to_latex(ccg_node[0], sem_tree, tokens)
        rule = ccg_node.get('rule')
        latex_str = get_fraction_latex(category_latex, latex_str_child, rule)
    elif len(ccg_node) > 0:
        latex_str_children = ''
        for child in ccg_node:
            latex_str_child = convert_node_to_latex(child, sem_tree, tokens)
            if latex_str_children == '':
                latex_str_children = latex_str_child
            else:
                latex_str_children = latex_str_children + " & " + latex_str_child
            # latex_str_children += latex_str_child
        rule = ccg_node.get('rule')
        latex_str = get_fraction_latex(category_latex, latex_str_children, rule)
    if sem_tree is not None and kDisplaySemantics:
        span_id = ccg_node.get('id')
        sem_node = find_node_by_id(span_id, sem_tree)
        semantics = sem_node.get('sem')
        semantics_latex = get_semantics_latex(semantics)
        latex_str = get_sem_latex(latex_str, semantics_latex)
    return latex_str

def get_sentence_surface_from_tokens(ccg_tokens, attribute = 'surf'):
    return ' '.join([token.get(attribute) for token in ccg_tokens])

def convert_doc_to_latex(doc, verbatim_strings = [], use_gold_trees=False):
    """
    This function expects a list of ccg_trees, and a list of tokens
    (as produced by transccg). Then, it converts each pair (ccg_tree, ccg_tokens)
    into a presentation MathML string, and wraps them with HTML code.
    verbatim_strings contains a list of strings that should be printed
    verbatim at the end of the HTML document, for debugging.
    """
    ccg_trees = []
    if use_gold_trees:
        for sentence in doc.xpath('//sentence'):
            gold_tree_index = int(sentence.get('gold_tree', '0'))
            ccg_trees.append(sentence.xpath('./ccg')[gold_tree_index])
        ccg_trees = [build_ccg_tree(c) for c in ccg_trees]
    else:
        ccg_trees = [build_ccg_tree(c) for c in doc.xpath('//sentence/ccg[1]')]
    sem_trees = [build_ccg_tree(c) for c in doc.xpath('//semantics')]
    if not sem_trees:
        sem_trees = [None] * len(ccg_trees)
    tokens = doc.xpath('//tokens')
    assert len(ccg_trees) == len(tokens) 
    num_hypotheses = len(ccg_trees) - 1
    sentence_ids = ["Premise {0}: ".format(i + 1) for i in range(num_hypotheses)]
    sentence_ids.append("Conclusion: ")
    latex_str = ""
    for i in range(len(ccg_trees)):
        sentence_surface = ' '.join(tokens[i].xpath('token/@surf'))
        latex_str += "\n\n\\vspace{2em}\n\n\\noindent\n" + sentence_ids[i] + sentence_surface + "\n\n\medskip\n\n" \
                    + convert_node_to_latex(ccg_trees[i], sem_trees[i], tokens[i])

    verbatim_text = ""
    if verbatim_strings:
       verbatim_text = "<p>Script piped to coq</p>"
       for vb_str in verbatim_strings:
           verbatim_text += "<pre>\n" + vb_str + "\n</pre>\n"

    html_str = "\documentclass{article}\n" \
             + "\\usepackage{proof,lscape}\n" \
             + "\\pagestyle{empty}\n" \
             + "\\newcommand{\\rulelabelsize}{\\scriptsize}\n" \
             + "\\newcommand{\\FA}{\\mbox{\\rulelabelsize $<$}}\n" \
             + "\\newcommand{\\BA}{\\mbox{\\rulelabelsize $>$}}\n" \
             + "\\newcommand{\\FC}{\\mbox{\\rulelabelsize $>\\!\\mathbf{B}$}}\n" \
             + "\\newcommand{\\BC}{\\mbox{\\rulelabelsize $>\\!\\mathbf{B}$}}\n" \
             + "\\newcommand{\\SR}[1]{\\begin{tabular}{c}$#1$\\end{tabular}}\n" \
             + "\\begin{document}\n" \
             + "\\small\n" \

    html_str += "%\\begin{landscape}"
    html_str += latex_str
    html_str += verbatim_text
    html_str += "\n%\\end{landscape}"
    html_str += "\n\\end{document}"
    return html_str
