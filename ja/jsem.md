# Running the RTE pipeline on JSeM.

If you have not done so already, first you need to download the Jigg CCG parser and its models by simply running in the console:

```bash
./ja/download_dependencies.sh
```

Then, you can run our RTE pipeline on JSeM as:

```
./ja/emnlp2016exp.sh 3 ja_emnlp2016
```

With the command above, you will do a problem-wise parallelization using 3 cores, and the results
will be stored in the directory `ja_emnlp2016`. To see the results in tabular form, you can do:

```bash
cat ja_emnlp2016/plain.results.table
cat ja_emnlp2016/gold.results.table
```

The first table shows the results using the 1-best CCG tree,
and the second table shows the results when using gold CCG trees.
You should see something like:

```
 ----------------------------------------------------------
    plain |   count| accuracy| recall| precision| av.speed| 
 ----------------------------------------------------------
       gq |    337 |   .7804 | .6877 |    .9681 |    2.31 |
   plural |     41 |   .5609 | .4193 |    .8666 |    1.74 |
adjective |     65 |   .6307 | .5714 |    .6857 |    1.29 |
     verb |     36 |   .7500 | .6896 |   1.0000 |     .94 |
 attitude |     44 |   .8636 | .7500 |   1.0000 |    1.43 |
    Total |    523 |   .7495 | .6541 |    .9265 |    1.97 |

 ----------------------------------------------------------
     gold |   count| accuracy| recall| precision| av.speed| 
 ----------------------------------------------------------
       gq |    337 |   .9228 | .8959 |    .9850 |    2.14 |
   plural |     41 |   .6829 | .5806 |    .9000 |    1.94 |
adjective |     65 |   .6769 | .6190 |    .7222 |    1.43 |
     verb |     36 |   .7777 | .7241 |   1.0000 |    1.02 |
 attitude |     44 |   .8863 | .7916 |   1.0000 |    1.48 |
    Total |    523 |   .8604 | .8126 |    .9494 |    1.90 |
```

You can see the parsing results in HTML form per section in the newly created `ja_emnlp2016` directory.

If you want to see the results but do not want to run the experiments, you can
uncompress the tgz file in `ja/ja_emnlp2016_results.tgz` and explore the directories and files within.
