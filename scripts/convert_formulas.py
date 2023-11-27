#!/usr/bin/python3
# -*- coding: utf-8 -*-

import argparse
from lxml import etree
import os
import sys
import textwrap

from nltk.sem.drt import *
from nltk2drs import convert_to_drs
from nltk2normal import remove_true, rename
from nltk2tptp import convert_to_tptp_proof
from logic_parser import lexpr

ARGS=None
DOCS=None

def get_formulas_from_xml(doc):
    formulas = []
    for f in doc.xpath('./sentences/sentence'):
        if f.xpath('semantics'):
            s = f.xpath('semantics')[0]
            if s.get('status') == 'success':
                formulas += s.xpath('span[1]/@sem')
            else:
                formulas.append('semantics_error')
        else:
            formulas.append('syntax_error')
    return formulas

def main(args = None):
    global ARGS
    global DOCS
    DESCRIPTION=textwrap.dedent("""\
            The input file sem should contain the parsed sentences. All CCG trees correspond
            to the premises, except the last one, which is the hypothesis.
      """)

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESCRIPTION)
    parser.add_argument("sem", help="XML input filename with semantics")

    parser.add_argument("--format", nargs='?', type=str, default="drs",
        choices=["fol", "drs", "notrue", "drsbox", "tptp"],
        help="Output format (default: drs).")

    ARGS = parser.parse_args()

    if not os.path.exists(ARGS.sem):
        print('File does not exist: {0}'.format(ARGS.sem), file=sys.stderr)
        parser.print_help(file=sys.stderr)
        sys.exit(1)

    parser = etree.XMLParser(remove_blank_text=True)
    root = etree.parse(ARGS.sem, parser)

    DOCS = root.findall('.//document')
    doc = DOCS[0]

    formulas = get_formulas_from_xml(doc)
    results  = []
    if ARGS.format == "tptp":
        inference = [lexpr(f) for f in formulas]
        results = convert_to_tptp_proof(inference)
    else:
        for formula in formulas:
            try:
                if ARGS.format == "drs" or ARGS.format == "drsbox":
                    results.append(convert_to_drs(lexpr(formula)))
                if ARGS.format == "fol":
                    results.append(convert_to_drs(lexpr(formula)).fol())
                if ARGS.format == "notrue":
                    results.append(rename(remove_true(lexpr(formula))))
            except:
                results.append('conversion_error')

    for formula in results:
        formula_str = str(formula)
        if ARGS.format == "drsbox":
            formula.pretty_print()
        print(formula_str)

if __name__ == '__main__':
    main()
