# Learning semantic textual similarity with ccg2lambda
The system for determining semantic textual similarity by combining shallow features with features with features extracted from natural deduction proofs of bidirectional entailment relations between sentence pairs

## Requirement
1. In order to run this system, you need to checkout a different branch at first:

```bash
git checkout emnlp2017_sts
```

2. You need to download some python modules, word2vec-api, the Jigg CCG parser and its models
by running the following script:

```bash
./ja/download_dependencies.sh
git clone https://github.com/3Top/word2vec-api
pip install -r requirements.txt
```

## Trial with sample text:
You can try extracting features for learning Japanese STS by doing:

```bash
./ja/similarity_ja_mp.sh sample.txt ja/semantic_templates_ja_event.yaml 
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
