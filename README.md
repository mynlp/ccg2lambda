# ccg2lambda: composing semantic representations guided by CCG derivations

This is a tool to derive formal semantic representations of
natural language sentences given CCG derivation trees and semantic templates.

## Installation

In order to run most part of this software, it is necessary to install python3,
nltk 3, lxml, simplejson and yaml python libraries. I recommend to use a python virtual environment,
and install the packages in the virtual environment with `pip`:

```bash
$ virtualenv --no-site-packages --distribute -p /usr/bin/python3 py3
$ source py3/bin/activate
(py3)$ pip install -I nltk==3.0.0
(py3)$ pip install lxml simplejson pyyaml
```

You also need to install WordNet:

```bash
(py3)$ python
>>> import nltk
>>> nltk.download('wordnet')
```

To ensure that all software is working as expected, you can run the tests:

```bash
(py3)$ cd ccg2lambda/
(py3)$ python run_tests.py
```
(all tests should pass, except a few expected failures).

Our system assigns semantics to CCG structures, as obtained by the [C&C parser](http://svn.ask.it.usyd.edu.au/trac/candc). In order to install the C&C parser, you may need to register, download the parser and the models, and follow their [instructions](http://svn.ask.it.usyd.edu.au/trac/candc/wiki/Installation) to set it up. For this software to find the C&C parser, please create a file `candc_location.txt` with the path to the C&C parser:

```bash
$ echo "/path/to/candc-1.00/" > candc_location.txt
```

Finally, please install the [Coq Proof Assistant](https://coq.inria.fr/) that we use for automated reasoning. In Ubuntu, you can install it by:

```bash
$ sudo apt-get install coq
```

Then, compile the coq library that contains the axioms:

```bash
$ coqc coqlib.v
```

## Running the pipeline.

First, you need to download the copy of [FraCaS provided by MacCartney and Manning (2007)](http://www-nlp.stanford.edu/~wcmac/downloads/fracas.xml):

```bash
$ wget http://www-nlp.stanford.edu/~wcmac/downloads/fracas.xml
```

You can evaluate the end-to-end system performance of a certain list of semantic templates on
fracas by doing:

```bash
./evaluate_template.sh semantic_templates_en_emnlp2015.yaml fracas.xml
```

This script will:

1. Extract the plain text corresponding to the hypotheses and conclusions of all fracas problems. These hypotheses and conclusions are stored in a different file for each fracas problem, under the directory `fracas.xml_plain`. The gold entailment judgment is stored in files `fracas.xml_plain/*.answer`.
2. Parse the hypotheses and conclusions using C&C parser, and save them under the directory `fracas.xml_parsed`.
3. Compose the semantics of each hypothesis and conclusion, and attempt inference using coq. Graphical HTML results of the composition are stored in `fracas.xml_results/*.html` directory together with the entailment judgment of the system (`fracas.xml_results/*.answer`).
A file `fracas.xml_results/main.html` is created listing all links to the graphical representation of each fracas problem. The background of each link has different colors (they do not relate to the computation of accuracies below).
  1. Green if the system's entailment decision coincides with the gold entailment decision.
  2. White if the system's entailment decision is either "unknown" or "undefined".
  3. Red if the system's entailment decision is not "unknown" and does not coincide with the gold entailment judgment.
  4. Gray if the system's entailment decision is unknown (or empty, if there was any pipeline error).
4. Compute accuracies per section as a three-way classification (yes, no, unknown) and print them to the console. E.g.:

```bash
Results ...
```

This script will not overwrite the directories with CCG-parsed sentences or entailment judgments, if present. If you would like any directory to be re-built, then you can remove it or rename it, and re-run the pipeline.

## Interpreting (and writing your own) semantic templates.

You can find our semantic templates in `semantic_templates_en.yaml`. Here are some notes:

1. Each Yaml block is a rule. If the rule matches the attributes of a CCG node, then the semantic template specified by "semantics" is applied. It is possible to write an arbitrary set of field names and their values. For example, you could specify the "category" of the CCG node and the surface "surf" form of a word (in case the CCG node is a leaf). Only the "category" field and the "semantics" field are compulsory.
2. If you underspecify the characteristics of a CCG node, the semantic rule will match more general CCG nodes. It is also possible to underspecify the features of syntactic categories.
3. If more than one rule applies, only the last one in the file will be applied.
4. Any CCG node can be matched by the semantic rules.
  1. If the rule matches a CCG leaf node, then the base form (or surface form, if base not present) will be passed as the first argument to the lambda expression of the semantic template (specified by "semantics" field in Yaml rule).
  2. If the rule matches a CCG node with only one child, then the semantic expression of the child will be passed as the first argument to the semantic template assigned to this CCG node.
  3. If the rule matches a CCG node with two children, then the semantic expressions of the left and right children will be passed as the first and second argument to the semantic template of this CCG node, respectively.
5. Rules that are intended to match inner nodes of the CCG derivation need to specify either:
  1. A "rule" attribute, specifying what type of combination operation is there.
  2. A "child" attribute, specifying at least one attribute of one child (see next point).
6. You can specify in a semantic rule the characteristics of the children at the current CCG node. To that purpose, simply prefix the attribute name with "child0\_" or "child1\_" of the left or right child, respectively. E.g. if you want to specify the syntactic category of the left child, then you call such attribute in the semantic rule as "child0\_category". You can still underspecify the attributes of the children. If the CCG node only has one child, then it is considered a left child (and its attributes are specified using "child0\_" as a prefix).

# Citing this work

If you use this software or semantic templates for your work, please consider citing it as:

* Koji Mineshima, Pascual Martínez-Gómez, Yusuke Miyao, Daisuke Bekki. Higher-order logical inference with compositional semantics. Proceedings of the 2015 Conference on Empirical Methods in Natural Language Processing, pages 2055–2061, Lisbon, Portugal, 17-21 September 2015. [pdf](http://www.emnlp2015.org/proceedings/EMNLP/pdf/EMNLP244.pdf)
