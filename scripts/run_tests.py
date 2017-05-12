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

from abduction_tools_test import GetPremisesThatMatchConclusionArgsTestCase
from abduction_tools_test import GetTreePredArgsTestCase
from category_test import CategoryTestCase
from ccg2lambda_tools_test import AssignSemanticsToCCGTestCase
from ccg2lambda_tools_test import AssignSemanticsToCCGWithFeatsTestCase
from ccg2lambda_tools_test import get_attributes_from_ccg_node_recursivelyTestCase
from ccg2lambda_tools_test import TypeRaiseTestCase
from knowledge_test import LexicalRelationsTestCase
from nltk2coq_test import Nltk2coqTestCase
from semantic_index_test import GetSemanticRepresentationTestCase
from semantic_tools_test import resolve_prefix_to_infix_operationsTestCase
from semantic_types_test import ArbiAutoTypesTestCase
from semantic_types_test import build_arbitrary_dynamic_libraryTestCase
from semantic_types_test import build_dynamic_libraryTestCase
from semantic_types_test import Coq2NLTKTypesTestCase
from semantic_types_test import Coq2NLTKSignaturesTestCase
from semantic_types_test import combine_signatures_or_rename_predsTestCase

if __name__ == '__main__':
    suite1  = unittest.TestLoader().loadTestsFromTestCase(AssignSemanticsToCCGTestCase)
    suite2  = unittest.TestLoader().loadTestsFromTestCase(AssignSemanticsToCCGWithFeatsTestCase)
    suite3  = unittest.TestLoader().loadTestsFromTestCase(TypeRaiseTestCase)
    suite4  = unittest.TestLoader().loadTestsFromTestCase(build_dynamic_libraryTestCase)
    suite5  = unittest.TestLoader().loadTestsFromTestCase(resolve_prefix_to_infix_operationsTestCase)
    suite6  = unittest.TestLoader().loadTestsFromTestCase(Nltk2coqTestCase)
    suite7  = unittest.TestLoader().loadTestsFromTestCase(build_arbitrary_dynamic_libraryTestCase)
    suite8  = unittest.TestLoader().loadTestsFromTestCase(LexicalRelationsTestCase)
    suite9  = unittest.TestLoader().loadTestsFromTestCase(Coq2NLTKTypesTestCase)
    suite10 = unittest.TestLoader().loadTestsFromTestCase(Coq2NLTKSignaturesTestCase)
    suite11 = unittest.TestLoader().loadTestsFromTestCase(ArbiAutoTypesTestCase)
    suite12 = unittest.TestLoader().loadTestsFromTestCase(get_attributes_from_ccg_node_recursivelyTestCase)
    suite13 = unittest.TestLoader().loadTestsFromTestCase(GetSemanticRepresentationTestCase)
    suite14 = unittest.TestLoader().loadTestsFromTestCase(GetTreePredArgsTestCase)
    suite15 = unittest.TestLoader().loadTestsFromTestCase(GetPremisesThatMatchConclusionArgsTestCase)
    suite16 = unittest.TestLoader().loadTestsFromTestCase(combine_signatures_or_rename_predsTestCase)
    suite17 = unittest.TestLoader().loadTestsFromTestCase(CategoryTestCase)
    suites  = unittest.TestSuite([suite1, suite2, suite3, suite4, suite5, suite6,
                                  suite7, suite8, suite9, suite10, suite11, suite12,
                                  suite13, suite14, suite15, suite16, suite17])
    unittest.TextTestRunner(verbosity=2).run(suites)
