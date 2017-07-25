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

import sys, os

def main():
    f = open("train/STS.input.MSRvid.txt", "r")
    train_inputs = f.readlines()
    f.close()
    g = open("train/STS.gs.MSRvid.txt", "r")
    train_answers = g.readlines()
    g.close()
    h = open("test-gold/STS.input.MSRvid.txt", "r")
    test_inputs = h.readlines()
    h.close()
    i = open("test-gold/STS.gs.MSRvid.txt", "r")
    test_answers = i.readlines()
    i.close()
    for num in range(1, 751):
        j = open("plain/sick_train_"+str(num)+".txt", "w")
        train_sentences = train_inputs[num-1].split("\t")
        j.write(train_sentences[0]+"\n"+train_sentences[1])
        j.close()
        k = open("plain2/sick_train_"+str(num)+".answer", "w")
        k.write(train_answers[num-1])
        k.close()
        l = open("plain/sick_test_"+str(num)+".txt", "w")
        test_sentences = test_inputs[num-1].split("\t")
        l.write(test_sentences[0]+"\n"+test_sentences[1])
        l.close()
        m = open("plain2/sick_test_"+str(num)+".answer", "w")
        m.write(test_answers[num-1])
        m.close()


if __name__ == '__main__':
    main()
