#!/bin/bash
#
# Download C&C from http://www.cl.cam.ac.uk/~sc609/
# 
# Refer to:
# 
# Stephen Clark and James Curran (2007): Wide-Coverage Efficient Statistical Parsing with CCG and Log-Linear Models. In Computational Linguistics 33(4), http://aclweb.org/anthology-new/J/J07/J07-4004.pdf

candc_url="http://www.cl.cam.ac.uk/~sc609/resources/candc-downloads/candc-linux-1.00.tgz"
models_url="http://www.cl.cam.ac.uk/~sc609/resources/candc-downloads/models-1.02.tgz"
parser_basename=`basename $candc_url`
models_basename=`basename $models_url`

test -d candc-1.00 || {
  test -f $parser_basename || {
    wget $candc_url
  }
  
  test -f $models_url || {
    wget $models_url
  }

  tar xvzf $parser_basename
  tar xvzf $models_basename --directory candc-1.00
}

parser_dir=`pwd`"/"candc-1.00
echo "Setting en/candc_location.txt pointing to ${parser_dir}"
echo $parser_dir > en/candc_location.txt
rm -f $parser_basename $models_basename

