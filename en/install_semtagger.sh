#!/bin/bash
#
# Download semtagger from https://github.com/ginesam/semtagger

semtagger_url="https://github.com/ginesam/semtagger.git"
semtagger_dir=`pwd`"/"semtagger

git clone https://github.com/ginesam/semtagger $semtagger_dir
echo $semtagger_dir > en/semtagger_location.txt

