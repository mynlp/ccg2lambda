# Learning semantic textual similarity with ccg2lambda
The system for determining semantic textual similarity by combining shallow features with features with features extracted from natural deduction proofs of bidirectional entailment relations between sentence pairs

## Requirement
1. In order to run this system, you need to checkout a different branch at first:

```bash
git checkout emnlp2017_sts
```

2. Ensure that you have downloaded [C&C parser](http://www.cl.cam.ac.uk/~sc609/candc-1.00.html)
and [EasyCCG parser](https://github.com/mikelewis0/easyccg) and wrote their installation locations
in the files `en/parser_location.txt`.
```bash
cat en/parser_location.txt
candc:/home/usr/software/candc/candc-1.00
easyccg:/home/usr/software/easyccg
```

3. You need to download some python modules,
the [SICK dataset](http://alt.qcri.org/semeval2014/task1/index.php?id=data-and-tools)
by running the following script:

```bash
./en/download_dependencies.sh
pip install -r requirements.txt
```

4. Also, you need to download pretrained vector space models from [Here](https://github.com/mynlp/ccg2lambda/files/1172401/models.zip). 
After that, unzip the `models.zip` file and put this `models` directory into the `en` directory.

## Evaluation with SemEval-2014 SICK dataset
You can evaluate the end-to-end system performance of a certain list of semantic templates on
the test split of SICK by doing:

```bash
./en/emnlp2017exp.sh 3 en/semantic_templates_en_event_sts.yaml
```

## Evaluation with SemEval-2012 MSR-video dataset  
You can also evaluate the system performance with MSR-video dataset by doing:

```bash
./en/emnlp2017exp_msr.sh 3 en/semantic_templates_en_event_sts.yaml
```

## Output
System output is shown below:
```bash
features_np.pickle(extracted features from ccg2lambda)
randomforestregressor.pkl(trained model)

results/evaluation.txt(correlation evaluation)
results/error_result.txt(error predictions (diff > 0.75))
results/all_result.txt(all the predictions)
results/result.png(regression line)
```
