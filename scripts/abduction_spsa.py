#!/usr/bin/python
# -*- coding: utf-8 -*-

from abduction_tools import TryAbductions

class AxiomsWordnet(object):
    """
    Create axioms using relations in WordNet.
    """
    def __init__(self):
        pass

    def attempt(self, coq_scripts, context=None):
        return TryAbductions(coq_scripts)

