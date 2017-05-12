# Running the RTE pipeline on SICK.

First, ensure that you have downloaded [C&C parser](http://www.cl.cam.ac.uk/~sc609/candc-1.00.html)
and [EasyCCG parser](https://github.com/mikelewis0/easyccg) and wrote their installation locations
in the files `en/candc_location.txt` and `en/easyccg_location.txt`, respectively.

Second, you need to download the [SICK dataset](http://alt.qcri.org/semeval2014/task1/index.php?id=data-and-tools)
and [VerbOcean](http://www.patrickpantel.com/download/data/verbocean/verbocean.unrefined.2004-05-20.txt.gz)
by running the following script:

```bash
./en/download_dependencies.sh
```

You can evaluate the end-to-end system performance of a certain list of semantic templates on
the test split of SICK by doing:

```bash
./en/eacl2017exp.sh 10 test en/semantic_templates_en_event.yaml
```

This script will coordinate the tokenization, syntactic parsing (with C&C and
EasyCCG), semantic parsing and theorem proving (with Coq) using 10 processes.
Syntactic and semantic parsing results will be written in `parsed` directory.
Entailment judgements and an HTML graphical representation of semantic
composition (and constructed theorem) will be written in `results` directory.
You can see a summary of performance by doing:

```bash
cat results/score.txt
```

and you should see something similar to this:

```
Correct parsing: 0.9748 (4803/4927)
Accuracy: 0.8313 (4096/4927)
Recall: 0.6265
Precision: 0.9688
F1 score: 0.7608
Gold_correct_total: 2134
System_answer_total: 1380
System_correct_total: 1337
----------------------------------------------------------------
                            system                              
     |        |     yes |      no | unknown |   error |   total 
----------------------------------------------------------------
     |     yes|     838 |       6 |     565 |       5 |    1414 
gold |      no|       3 |     499 |     176 |      42 |     720 
     | unknown|      22 |      12 |    2682 |      77 |    2793 
     |   total|     863 |     517 |    3423 |     124 |    4927 
----------------------------------------------------------------
```

If you want to see the results (syntactic/semantic parses, entailment judgements and HTML
visualizations) but do not wish to run the software, you can uncompress the file
`en/sick_intermediate_results.tgz` by doing:

```bash
tar xvzf en/sick_intermediate_results.tgz
```

which will create the `plain/`, `parsed/` and `results/` directories.
