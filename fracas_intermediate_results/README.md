# Our intermediate results when running ccg2lambda on FraCaS

This folder contains our intermediate results when running ccg2lambda on FraCaS. There are three folders:

`fracas.xml_plain`: contains three files for each entailment problem:

* `<problem>`.answer is the gold entailment judgement.
* `<problem>`.txt has the plain-text premises, one per line, except the last line which is the conclusion.
* `<problem>`.tok has the tokenized text.

`fracas.xml_parsed`: contains three main files for each entailment problem:

* `<problem>`.tok.candc.xml is the CCG derivation by the C&C parser (version 1.00).
* `<problem>`.xml is the Jigg-style (similar to coreNLP's style) XML conversion of the file above.
* `<problem>`.sem.xml is the semantically-augmented CCG derivation of the file above.

`fracas.xml_results`: contains two main files for each entailment problem:

* `<problem>`.answer is the entailment judgement of ccg2lambda (yes, no or unknown).
* `<problem>`.html is the HTML plot of the semantically-augmented CCG derivation,
  and the scripts piped to Coq with the parameter definitions and theorems.

Please let us know if your results for FraCaS (when using ccg2lambda) differ from the results in this directory.

