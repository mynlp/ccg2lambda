# Running the RTE pipeline on FraCas.

First, ensure that you have downloaded C&C parser and wrote its location in the file `en/candc_location.txt`.

Second, you need to download the copy of [FraCaS provided by MacCartney and Manning (2007)](http://www-nlp.stanford.edu/~wcmac/downloads/fracas.xml):

```bash
$ wget --no-check-certificate http://www-nlp.stanford.edu/~wcmac/downloads/fracas.xml
```

You can evaluate the end-to-end system performance of a certain list of semantic templates on
fracas by doing:

```bash
git checkout tags/fracas
./en/emnlp2015exp.sh en/semantic_templates_en_emnlp2015.yaml fracas.xml
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
                              all premi.          single           multi
generalized_quantifiers   |      0.78      |      0.82      |      0.73     
plurals                   |      0.67      |      0.67      |      0.67     
adjectives                |      0.68      |      0.87      |      0.29     
comparatives              |      0.48      |      0.62      |      0.33     
attitudes                 |      0.77      |      0.78      |      0.75     
verbs                     |      0.62      |      0.62      |      ----     
total                     |      0.69      |      0.75      |      0.58     
```

This script will not overwrite the directories with CCG-parsed sentences or entailment judgments, if present. If you would like any directory to be re-built, then you can remove it or rename it, and re-run the pipeline.

