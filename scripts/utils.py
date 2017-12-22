#!/usr/bin/python
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

import logging
import time

def time_count(fn):
  # Funtion wrapper used to measure time consumption
  def _wrapper(*args, **kwargs):
    start = time.clock()
    returns = fn(*args, **kwargs)
    logging.debug("[time_count]: %s took %fs" % (fn.__name__, time.clock() - start))
    return returns
  return _wrapper

