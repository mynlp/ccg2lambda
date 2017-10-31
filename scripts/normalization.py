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

import re

def normalize_token(token):
    """
    Convert symbols to avoid collisions with reserved punctuation
    in NLTK and coq.
    To avoid collisions with reserved words, we prefix each token
    with an underscore '_'.
    """
    normalized = token
    normalized = re.sub(r'\.', '_DOT', normalized)
    normalized = re.sub(r',', '_COMMA', normalized)
    normalized = re.sub(r'\(', '_LEFTB', normalized)
    normalized = re.sub(r'\)', '_RIGHTB', normalized)
    normalized = re.sub(r'^-$', '_HYPHEN', normalized)
    normalized = re.sub(r'^&$', '_AMPERSAND', normalized)
    normalized = re.sub(r'!', '_EXCLAMATION', normalized)
    normalized = re.sub(r'-', '_dash_', normalized)
    if not normalized.startswith('_'):
        normalized = '_' + normalized
    return normalized

def denormalize_token(token):
    """
    Unconvert symbols. This is the reverse operation as above.
    """
    denormalized = token
    denormalized = re.sub('_DOT', r'\.', denormalized)
    denormalized = re.sub('_COMMA', r',', denormalized)
    denormalized = re.sub('_LEFTB', r'\(', denormalized)
    denormalized = re.sub('_RIGHTB', r'\)', denormalized)
    denormalized = re.sub('_HYPHEN', r'^-$', denormalized)
    denormalized = re.sub('_AMPERSAND', r'^&$', denormalized)
    denormalized = re.sub('_EXCLAMATION', r'!', denormalized)
    denormalized = re.sub('_dash_', r'-', denormalized)
    # Remove possible suffix that was introduced to avoid type clashes.
    denormalized = re.sub(r'_[a-z][0-9]$', '', denormalized)
    denormalized = denormalized.lstrip('_')
    return denormalized

