# -*- coding: utf-8 -*-
#
#  Copyright 2015 Pascual Martinez-Gomez
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

from nltk import FeatStruct
import re

class Category(object):
    """ Implements a CCG syntactic category with features. """

    def __init__(self, category):
        if isinstance(category, self.__class__):
            self.types = category.types
            self.type_features = category.type_features
        else:
            self.types = remove_feats_from_category(category)
            self.type_features = get_feats_from_category(category)

    def __repr__(self):
        return "Types: {0}\tFeats: {1}".format(self.types, self.type_features)

    def match(self, other):
        if not isinstance(other, self.__class__):
            return False
        if len(self.type_features) != len(other.type_features):
            return False
        # TODO: Ideally these substitutions should be precomputed for speed-up.
        types = re.sub(r'\\', r'\\\\', self.types)
        types = types.replace('|', '[/\\\]')
        types = types.replace('(', '\\(').replace(')', '\\)')
        if not re.fullmatch(types, other.types):
            return False
        return all([a.subsumes(b)
                    for (a, b) in zip(self.type_features, other.type_features)])

    def match_(self, other):
        return isinstance(other, self.__class__) \
          and len(self.type_features) == len(other.type_features) \
          and re.fullmatch(re.sub(r'\\', r'\\\\', self.types), other.types) \
          and all([a.subsumes(b) \
                   for (a, b) in zip(self.type_features, other.type_features)])

    def get_num_args(self):
        return len(self.type_features) - 1

def get_feats_from_category(category):
    r""" Returns the features of the syntactic category.
    category="S[mod=nm,form=base]" --> feats=['[mod=nm,form=base]']
    category="(S/S)\NP[mod=nm,case=nc]" --> feats=['', '', '[mod=nm,case=nc]']
    category="S[mod=nm,form=base]\NP[mod=nm,case=nc]" -->
      feats=['[mod=nm,form=base]', '[mod=nm,case=nc]']
    """
    feature_strings = re.findall(r'\w+(\[.+?\])*', category)
    features = []
    for feature_str in feature_strings:
        if feature_str == '':
            feature = FeatStruct({})
        else:
            attribute_value_dict = {}
            for attribute_value in feature_str.strip('[]').split(','):
                [attribute, value] = attribute_value.split('=')
                attribute_value_dict[attribute] = value
            feature = FeatStruct(attribute_value_dict)
        features.append(feature)
    return features

def remove_feats_from_category(category):
    r""" Remove features from syntactic category and returns only the category.
    category="S[mod=nm,form=base]" --> category="S"
    category="(S/S)\NP[mod=nm,case=nc]" --> category="(S/S)\NP"
    category="S[mod=nm,form=base]\NP[mod=nm,case=nc]" --> category="S\NP"
    """
    return re.sub(r'\[.+?\]', '', category)
