#!/usr/bin/python3
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

import unittest

from nltk.sem.logic import read_type
from logic_parser import lexpr

from semantic_types import resolve_types
from semantic_types import combine_signatures_or_rename_preds

class combine_signatures_or_rename_predsTestCase(unittest.TestCase):
    def test_different_onepred(self):
        exprs = [lexpr(r'pred1(x)'), lexpr(r'pred2(x)')]
        sigs = [resolve_types(e) for e in exprs]
        sig, exprs_new = combine_signatures_or_rename_preds(sigs, exprs)
        self.assertEqual(3, len(sig), msg='Unexpected signature: {0}'.format(sig))
        self.assertEqual(exprs, exprs_new)

    def test_equal_onepred(self):
        exprs = [lexpr(r'pred1(x)'), lexpr(r'pred1(x)')]
        sigs = [resolve_types(e) for e in exprs]
        sig, exprs_new = combine_signatures_or_rename_preds(sigs, exprs)
        self.assertEqual(2, len(sig), msg='Unexpected signature: {0}'.format(sig))
        self.assertEqual(exprs, exprs_new)

    def test_equalvar_onepred(self):
        exprs = [lexpr(r'pred1(x)'), lexpr(r'pred1(y)')]
        sigs = [resolve_types(e) for e in exprs]
        sig, exprs_new = combine_signatures_or_rename_preds(sigs, exprs)
        self.assertEqual(3, len(sig), msg='Unexpected signature: {0}'.format(sig))
        self.assertEqual(exprs, exprs_new)

    def test_different_one_two_pred(self):
        exprs = [lexpr(r'pred1(x)'), lexpr(r'pred1(x,y)')]
        sigs = [resolve_types(e) for e in exprs]
        sig, exprs_new = combine_signatures_or_rename_preds(sigs, exprs)
        self.assertEqual(4, len(sig), msg='Unexpected signature: {0}'.format(sig))
        self.assertEqual(exprs[0], exprs_new[0])
        self.assertNotEqual(exprs[1], exprs_new[1])

    def test_different_one_pred_vartype(self):
        exprs = [lexpr(r'pred1(x)'), lexpr(r'pred1(F)')]
        sigs = [resolve_types(e) for e in exprs]
        sig, exprs_new = combine_signatures_or_rename_preds(sigs, exprs)
        self.assertEqual(4, len(sig), msg='Unexpected signature: {0}'.format(sig))
        self.assertEqual(exprs[0], exprs_new[0])
        self.assertNotEqual(exprs[1], exprs_new[1])

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(combine_signatures_or_rename_predsTestCase)
    suites  = unittest.TestSuite([suite1])
    unittest.TextTestRunner(verbosity=2).run(suites)
