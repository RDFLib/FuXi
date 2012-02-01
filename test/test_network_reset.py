#!/usr/bin/env python
# encoding: utf-8
import unittest
try:
    from rdflib import Graph
except ImportError:
    from rdflib.Graph import Graph
from FuXi.Rete.RuleStore import SetupRuleStore

## fix for bug in reset method which didn't initialise
## network.inferredFacts properly if the provided graph
## was empty
## http://code.google.com/p/fuxi/issues/detail?id=17
##

class NetworkReset(unittest.TestCase):
    def setUp(self):
	    self.rule_store, self.rule_graph, self.network = SetupRuleStore(makeNetwork=True)
    def testReset(self):
        newInferredFacts = Graph()
        self.network.reset(newInferredFacts)
        self.failUnless(newInferredFacts is self.network.inferredFacts)		
    
if __name__ == '__main__':
	unittest.main()
