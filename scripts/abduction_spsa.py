#!/usr/bin/python
# -*- coding: utf-8 -*-

from abduction_tools import try_abductions

class AxiomsWordnet(object):
    """
    Create axioms using relations in WordNet.
    """
    def __init__(self):
        pass

    def attempt(self, coq_scripts, context=None):
        return try_abductions(coq_scripts)

