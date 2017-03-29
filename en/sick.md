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
Correct parsing: .9776 (4817/4927)
Accuracy: .8313 (4096/4927)
Recall: .6269
Precision: .9681
F1 score: .7610
Gold_correct_total: 2134
System_answer_total: 1382
System_correct_total: 1338
----------------------------------------------------------------
                            system                              
     |        |      yes|       no|  unknown|    error|    total
----------------------------------------------------------------
     |     yes| 838| 6| 567| 3| 1414
gold |      no| 3| 500| 177| 40| 720
     | unknown| 22| 13| 2691| 67| 2793
     |   total| 863| 519| 3435| 110| 4927
----------------------------------------------------------------
```


