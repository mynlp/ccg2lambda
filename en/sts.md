# learning textual similarity with ccg2lambda

First, ensure that you have downloaded [C&C parser](http://www.cl.cam.ac.uk/~sc609/candc-1.00.html)
and [EasyCCG parser](https://github.com/mikelewis0/easyccg) and wrote their installation locations
in the files `en/candc_location.txt` and `en/easyccg_location.txt`, respectively.

Second, you need to download some python modules,
the [SICK dataset](http://alt.qcri.org/semeval2014/task1/index.php?id=data-and-tools)
by running the following script:

```bash
./en/download_dependencies.sh
pip install -r requirements.txt
```

Then, you can evaluate the end-to-end system performance of a certain list of semantic templates on
the test split of SICK by doing:

```bash
./en/emnlp2017exp.sh 3 en/semantic_templates_en_event_sts.yaml
```

with SemEval-2012 dataset(SMT-europerl, MSR-vid, MSR-paraphrase)  
2. run another evaluation program(scripts/randomforest_2012.py) at the top directory
```bash
./en/emnlp2017exp_msr.sh 3 en/semantic_templates_en_event_sts.yaml
```

Outputs are shown below:
```bash
features_np.pickle(features)
randomforestregressor.pkl(model)

results/evaluation.txt(correlation evauation)
results/error_result.txt(error predictions (diff > 0.75))
results/all_result.txt(all the predictions)
results/result.png(regression line)
```
