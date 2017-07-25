# Learning textual similarity with ccg2lambda

In order to run this system, you need to checkout a different branch:

```bash
git checkout emnlp2017_sts
```

Then, ensure that you have downloaded [C&C parser](http://www.cl.cam.ac.uk/~sc609/candc-1.00.html)
and [EasyCCG parser](https://github.com/mikelewis0/easyccg) and wrote their installation locations
in the files `en/parser_location.txt`.
```bash
cat en/parser_location.txt
candc:/home/usr/software/candc/candc-1.00
easyccg:/home/usr/software/easyccg
```
Second, you need to download some python modules,
the [SICK dataset](http://alt.qcri.org/semeval2014/task1/index.php?id=data-and-tools),
and pretrained vector spaced models
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

with SemEval-2012 dataset(MSR-video)  
2. run another evaluation program at the top directory
```bash
./en/emnlp2017exp_msr.sh 3 en/semantic_templates_en_event_sts.yaml
```

Outputs are shown below:
```bash
features_np.pickle(extracted features from ccg2lambda)
randomforestregressor.pkl(trained model)

results/evaluation.txt(correlation evaluation)
results/error_result.txt(error predictions (diff > 0.75))
results/all_result.txt(all the predictions)
results/result.png(regression line)
```
