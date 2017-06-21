#!/usr/bin/python3
# -*- coding: utf-8 -*-
#
#  Copyright 2017 Pascual Martinez-Gomez
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

import fileinput
import json

def main(args = None):

    rel2label = {'entailment': 'yes', 'contradiction': 'no', 'neutral': 'unknown'}
    for line in fileinput.input():
        data = json.loads(line.strip())
        pair_id = data.get('set', 'train') + '_' + data.get('pairID', '0')
        doc_label = {
            'pair_id': pair_id,
            'set': data.get('set', 'train'),
            'rte_label': rel2label.get(data.get('gold_label', 'neutral'), 'unknown'),
            'sts_label': data.get('similarity', '-1')}
        print(json.dumps(doc_label))


if __name__ == '__main__':
    main()

