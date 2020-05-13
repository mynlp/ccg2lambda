#!/bin/bash
#
# Download C&C from https://sites.google.com/site/stephenclark609/resources/c-c_parser
#
# Refer to:
#
# Stephen Clark and James Curran (2007): Wide-Coverage Efficient Statistical Parsing with CCG and Log-Linear Models. In Computational Linguistics 33(4), http://aclweb.org/anthology-new/J/J07/J07-4004.pdf

# for MacOS
# candc_url="https://drive.google.com/uc?id=1vl9rwQDqhy5dmt8D8EnEPTGw9zqK0KSz"
# for Linux
candc_url="https://drive.google.com/uc?id=1MAqE0RmAC1sOW6A9ErpQcFmFbzD66i7x"

models_id=1LR6h3rX7a4Dq7fV_bc2mEmeYxteSyenH
parser_basename=`basename $candc_url`
models_basename=models-1.02.tgz

test -d candc-1.00 || {
  test -f $parser_basename || {
    wget $candc_url
  }
  curl -sc /tmp/cookie "https://drive.google.com/uc?export=download&id=${models_id}" > /dev/null
  CODE="$(awk '/_warning_/ {print $NF}' /tmp/cookie)"
  curl -Lb /tmp/cookie "https://drive.google.com/uc?export=download&confirm=${CODE}&id=${models_id}" -o $models_basename

  tar xvzf $parser_basename
  tar xvzf $models_basename --directory candc-1.00
}

parser_dir=`pwd`"/"candc-1.00
echo "Setting en/parser_location.txt pointing to ${parser_dir}"
echo $parser_dir > en/parser_location.txt
rm -f $parser_basename $models_basename
