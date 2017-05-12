#!/bin/bash

if [ ! -d "ja/jigg-v-0.4" ]; then
  echo "Downloading Jigg Japanese CCG parser into ja/ ."
  wget https://github.com/mynlp/jigg/archive/v-0.4.tar.gz -P ja/
  tar xzf ja/v-0.4.tar.gz -C ja/
  # CCG models.
  wget https://github.com/mynlp/jigg/releases/download/v-0.4/ccg-models-0.4.jar -P ja/jigg-v-0.4/jar/
  echo $PWD"/ja/jigg-v-0.4" > ja/jigg_location.txt
fi


