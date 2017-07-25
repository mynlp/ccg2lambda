#!/usr/bin/python
# -*- coding: utf-8 -*-

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
    for num in range(1, 750):
        j = open("plain/sick_train_"+str(num)+".txt", "w")
        train_sentences = train_inputs[num].split("\t")
        j.write(train_sentences[0]+"\n"+train_sentences[1])
        j.close()
        k = open("plain2/sick_train_"+str(num)+".answer", "w")
        k.write(train_answers[num])
        k.close()
        l = open("plain/sick_test_"+str(num)+".txt", "w")
        test_sentences = test_inputs[num].split("\t")
        l.write(test_sentences[0]+"\n"+test_sentences[1])
        l.close()
        m = open("plain2/sick_test_"+str(num)+".answer", "w")
        m.write(test_answers[num])
        m.close()


if __name__ == '__main__':
    main()