#!/usr/bin/python
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Hitomi Yanaka
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.


import os
import numpy as np
import scipy as sp
from scipy.stats import pearsonr, spearmanr
from sklearn.ensemble import RandomForestRegressor, RandomForestClassifier
from sklearn.grid_search import GridSearchCV
from sklearn.metrics import mean_squared_error, classification_report
import sys
import matplotlib.pyplot as plt
import random
import difflib
import feature_extraction

from sklearn.pipeline import make_pipeline
from sklearn import preprocessing
from sklearn import linear_model
from sklearn.feature_selection import SelectFromModel
from sklearn.externals import joblib
import re


from sklearn.cross_validation import cross_val_score

def crossvalidation(clf, X_train, y_train):
    scores = cross_val_score(clf, X_train, y_train, cv=10)
    return scores.mean(), scores.std()

def regression(X_train, y_train, X_test, y_test):
    parameters = {
        'n_estimators'      : [10, 50, 100, 200, 300],
        'random_state'      : [0],
        'n_jobs'            : [200],
        'max_features'      : ['auto', 'log2', 'sqrt', None],
        'criterion'         : ['mse'],
        'max_depth'         : [3, 5, 10, 20, 30, 40, 50, 100]
    }

    clf = make_pipeline(
        #preprocessing.StandardScaler(),
        preprocessing.MinMaxScaler(),
        GridSearchCV(RandomForestRegressor(), parameters))
    clf.fit(X_train, y_train)

    #Serialize
    joblib.dump(clf, 'randomforestregressor_wnw2v_sick.pkl')
    #clf = joblib.load('randomforestregressor_wnw2v_sick.pkl')

    return clf

def get_features(line):
    print("sick_id:{0}".format(line[0]))
    if line[14] == "0":
        line[14] = "1"
    if line[22] == "0":
        line[22] = "1"
    unknown1, yes1, no1 = 0, 0, 0
    unknown2, yes2, no2 = 0, 0, 0
    if line[4] == "0":
        unknown1 = 1.0
        yes1 = 0.0
        no1 = 0.0
    elif line[4] == "0.5":
        unknown1 = 0.0
        yes1 = 0.0
        no1 = 1.0
    elif line[4] == "1":
        unknown1 = 0.0
        yes1 = 1.0
        no1 = 0.0
    if line[8] == "0":
        unknown2 = 1.0
        yes2 = 0.0
        no2 = 0.0
    elif line[8] == "0.5":
        unknown2 = 0.0
        yes2 = 0.0
        no2 = 1.0
    elif line[8] == "1":
        unknown2 = 0.0
        yes2 = 1.0
        no2 = 0.0
    sentence1_list = line[2].split()
    sentence2_list = line[3].split()
    features = [
        unknown1,
        yes1,
        no1,
        unknown2,
        yes2,
        no2,   
        float(line[5]),                     #6 axiom similarity A->B #6
        0.5**float(line[6]),                #7 axiom number A->B
        float(line[7]),                     #8 final subgoal A->B #8
        float(line[9]),                     #9 axiom similarity B->A #9
        0.5**float(line[10]),               #10 axiom number B->A
        float(line[11]),                    #11 final subgoal B->A #11
        float(line[12]),                    #12 original subgoal A->B
        float(line[13]),                    #13 original subgoal B->A
        float(line[14]),                    #14 step A->B
        float(line[15])/float(line[14]),    #15-21 inference rule A->B 
        float(line[16])/float(line[14]),
        float(line[17])/float(line[14]),
        float(line[18])/float(line[14]),
        float(line[19])/float(line[14]),
        float(line[20])/float(line[14]),
        float(line[21])/float(line[14]),
        float(line[22]),                    #22 step B->A
        float(line[23])/float(line[22]),    #23-29 inference rule B->A 
        float(line[24])/float(line[22]),
        float(line[25])/float(line[22]),
        float(line[26])/float(line[22]),
        float(line[27])/float(line[22]),
        float(line[28])/float(line[22]),
        float(line[29])/float(line[22]),
        float(line[30]),                    #30-35 subgoal case A->B, B->A #30-35
        float(line[31]),
        float(line[32]),
        float(line[33]),
        float(line[34]),
        float(line[35]),
        float(feature_extraction.get_overlap(sentence1_list, sentence2_list)),                 #36 word overlap
        float(feature_extraction.sentence_lengths(sentence1_list, sentence2_list)),            #37 sentence length
        float(difflib.SequenceMatcher(None, line[2], line[3]).ratio()),                        #38 string similarity
        float(feature_extraction.word_overlap2(sentence1_list, sentence2_list)),               #39 Proportion of word overlap
        float(feature_extraction.sentence_lengths_difference(sentence1_list, sentence2_list)), #40 Proportion of difference in sentence length
        float(feature_extraction.synset_overlap(sentence1_list, sentence2_list)),              #41 Proportion of synset lemma overlap
        float(feature_extraction.synset_distance(sentence1_list, sentence2_list)),             #42 Synset distance
        float(feature_extraction.type_overlap(line[0])),                                       #43 type overlap
        float(feature_extraction.pos_overlap(line[0])),                                        #44 pos-tag overlap
        float(feature_extraction.noun_overlap(line[0])),                                       #45 Proportion of noun overlap
        float(feature_extraction.verb_overlap(line[0])),                                       #46 Proportion of verb overlap
        float(feature_extraction.pred_overlap(line[0])),                                       #47 Proportion of predicate overlap
        float(feature_extraction.tfidf(line[0])),                                              #48 tfidf
        float(feature_extraction.lsi(line[0])),                                                #49 LSI
        float(feature_extraction.lda(line[0])),                                                #50 LDA
        float(line[38]),                                                                       #51 tree-mapping features
        float(feature_extraction.passive_overlap(line[0])),                                    #52 passive overlap 2017/02/14
        float(feature_extraction.negation_overlap(line[0])),                                   #53 negation overlap 2017/02/14
    ]   
    return features


def retrieve_features(recalc=None, sick_train=None, sick_test=None):
    if recalc:
        # Extract training features and targets
        print ('Feature extraction (train)...')
        train_sources = np.array([get_features(line) for line in sick_train])
        train_targets = np.array([float(line[1]) for line in sick_train])

        # Extract trial features and targets
        print ('Feature extraction (trial)...')
        trial_sources = np.array([get_features(line) for line in sick_test])
        trial_targets = np.array([float(line[1]) for line in sick_test])
        
        # Save SICK ID
        train_id = np.array([line[0] for line in sick_train])
        trial_id = np.array([line[0] for line in sick_test])

        # Store to pickle for future reference
        with open('features_wnw2v_sick_np.pickle', 'wb') as out_f:
            np.save(out_f, train_sources)
            np.save(out_f, train_targets)
            np.save(out_f, trial_sources)
            np.save(out_f, trial_targets)
            np.save(out_f, train_id)
            np.save(out_f, trial_id)
    else:
        with open('features_wnw2v_sick_np.pickle', 'rb') as in_f:
            train_sources = np.load(in_f)
            train_targets = np.load(in_f)
            trial_sources = np.load(in_f)
            trial_targets = np.load(in_f)
            train_id = np.load(in_f)
            trial_id = np.load(in_f)
    return train_sources, train_targets, trial_sources, trial_targets

def plot_deviation(outputs, actual):
    plt.figure(figsize=(12, 6))
    plt.subplot(1, 2, 1)
    plt.title('Comparison')

    zipped = sorted(zip(outputs, actual), key=lambda x: x[1])
    outputs = [i[0] for i in zipped]
    actual = [i[1] for i in zipped]


    plt.plot(np.arange(len(outputs)) + 1, outputs, 'b.', 
        label='Predicted values')
    plt.plot(np.arange(len(outputs)) + 1, actual, 'r-', 
        label='Actual values')

    plt.legend(loc='upper left')
    plt.xlabel('Sentence no.')
    plt.ylabel('Relatedness')

    plt.savefig('./results/result.png', bbox_inches='tight')

def write_for_evaluation(outputs, sick_ids, trial_targets):
    with open('./results/all_result.txt', 'w') as out_f:
        out_f.write('pair_ID\tentailment_judgment\trelatedness_score\tcorrect_answer\n')
        for i, line in enumerate(outputs):
            data = line
            # Fix that predictions are sometimes out of range
            if data > 5.0:
                data = 5.0
            elif data < 1.0:
                data = 1.0
            if os.path.isfile('./plain/sick_test_'+sick_ids[i]+'.answer'):
                j = open('./plain/sick_test_'+sick_ids[i]+'.answer', 'r')
                entailment = j.readlines()[0].strip()
                j.close()
                out_f.write('{0}\t{1}\t{2}\t{3}\n'.format(sick_ids[i], entailment, data, trial_targets[i]))
            elif os.path.isfile('./plain/sick_train_'+sick_ids[i]+'.answer'):
                j = open('./plain/sick_train_'+sick_ids[i]+'.answer', 'r')
                entailment = j.readlines()[0].strip()
                j.close()
                out_f.write('{0}\t{1}\t{2}\t{3}\n'.format(sick_ids[i], entailment, data, trial_targets[i]))
            elif os.path.isfile('./plain/sick_trial_'+sick_ids[i]+'.answer'):
                j = open('./plain/sick_trial_'+sick_ids[i]+'.answer', 'r')
                entailment = j.readlines()[0].strip()
                j.close()
                out_f.write('{0}\t{1}\t{2}\t{3}\n'.format(sick_ids[i], entailment, data, trial_targets[i]))


def output_errors(outputs, gold, sick_ids, sick_sentences):
    with open('./results/error_result.txt', 'w') as out_f:
        out_f.write('pair_ID\tdiff\tpred\tcorr\tsentence1\tsentence2\n')
        errs = []
        for i, line in enumerate(outputs):
            data = line
            corr = gold[i]
            diff = abs(data-corr)
            if diff > 0.75:
                errs.append([sick_ids[i], round(diff, 1), round(data, 1), corr, sick_sentences[i][0], sick_sentences[i][1]])

        errs.sort(key=lambda x:-x[1])

        for line in errs:
            out_f.write('{0}\t{1}\t{2}\t{3}\t{4}\t{5}\n'.format(*line))



def load_sick_data_from(sick_id, kind):
    line = []
    line.append(sick_id)
    f = open('./plain2/sick_'+kind.lower()+'_'+sick_id+'.answer', 'r')
    line.append(f.readlines()[0].strip())
    f.close()

    g = open('./plain/sick_'+kind.lower()+'_'+sick_id+'.txt', 'r')
    texts = g.readlines()
    line.append(texts[0].strip())
    line.append(texts[1].strip())
    g.close()
    if os.path.exists('./results/sick_'+kind.lower()+'_'+sick_id+'.answer'):
        h = open('./results/sick_'+kind.lower()+'_'+sick_id+'.answer', 'r')
        result = h.readlines()
        if result and not re.search("coq_error", result[0]) and not "unknown\n" in result:
            results = result[0].split(",")
            for r in results:
                r = r.strip("[] \n")
                line.append(r)
        else:
            return None
        h.close()
    else:
        return None

    i = open('./plain/sick_'+kind.lower()+'_'+sick_id+'.tok', 'r')
    texts = i.readlines()
    line.append(texts[0].strip())
    line.append(texts[1].strip())
    i.close()

    j = open('./tmp/sick.mapping_costs.new.txt')
    scores = j.readlines()
    for score in scores:
        if re.search('^plain/sick_'+kind.lower()+'_'+sick_id+'.txt', score):
            line.append(score.split()[1].strip())
            break
    if len(line) == 38:
        line.append("0.0")
    j.close()

    return line

def load_sick_data():
    sick_train, sick_test = [], []
    for line in open('./en/SICK.semeval.txt'):
        if line.split('\t')[0] != 'pair_ID' and line.split('\t')[-1].strip() == 'TRAIN':
            if load_sick_data_from(line.split('\t')[0], 'TRAIN') is not None:
                sick_train.append(load_sick_data_from(line.split('\t')[0], 'TRAIN'))
        if line.split('\t')[0] != 'pair_ID' and line.split('\t')[-1].strip() == 'TRIAL':
            if load_sick_data_from(line.split('\t')[0], 'TRIAL') is not None:
                sick_train.append(load_sick_data_from(line.split('\t')[0], 'TRIAL'))
        if line.split('\t')[0] != 'pair_ID' and line.split('\t')[-1].strip() == 'TEST':
            if load_sick_data_from(line.split('\t')[0], 'TEST') is not None:
                sick_test.append(load_sick_data_from(line.split('\t')[0], 'TEST'))
       # if len(sick_train) == 10:
       #     break
    return sick_train, sick_test

## spearman correlation
def spearman(x, y):
    N = len(x)
    return 1 - (6 * sum(x - y) ** 2) / float(N**3 - N)

## root mean squared arror
def rmse(x, y):
    ## x:targets y:predictions
    return np.sqrt(((y - x) ** 2).mean())

def main():
    # Load sick data
    sick_train, sick_test = load_sick_data()
    random.seed(23)
    random.shuffle(sick_train)
    random.shuffle(sick_test)
    print ('test size: {0}, training size: {1}'.format(len(sick_test), len(sick_train)))

    # Get training and trial features
    train_sources, train_targets, trial_sources, trial_targets = retrieve_features(1, sick_train, sick_test)
    #train_sources, train_targets, trial_sources, trial_targets = retrieve_features()
        
    # Train the regressor
    clf = regression(train_sources, train_targets, trial_sources, trial_targets)

    # Apply regressor to trial data
    outputs = clf.predict(trial_sources)
    trial_targets = np.array([float(line[1]) for line in sick_test])

    # Evaluate regressor
    write_for_evaluation(outputs, [line[0] for line in sick_test], trial_targets) #Outputs and sick_ids

    # Check errors
    output_errors(outputs, trial_targets, [line[0] for line in sick_test], [line[2:4] for line in sick_test]) #Outputs and sick_ids

    # Plot deviations
    #plot_deviation(outputs, trial_targets)

    x = np.loadtxt(outputs, dtype=np.float32)
    y = np.loadtxt(trial_targets, dtype=np.float32)
    with open('./results/evaluation.txt', 'w') as eval_f:
        ## pearson correlation
        r, p = pearsonr(x, y)
        eval_f.write('pearson correlation: {r}\n'.format(r=r))

        ## spearman correlation
        r, p = spearmanr(x, y)
        eval_f.write('spearman correlation: {r}\n'.format(r=r))

        ## mean squared error(rmse)
        score = rmse(x, y)
        eval_f.write('mean squared error:{0}\n'.format(score))
    

if __name__ == '__main__':
    main()
