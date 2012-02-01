#!/bin/env python
import unittest
from FuXi.Syntax.InfixOWL import *
from FuXi.Rete.Network import ReteNetwork
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.DLP import SKOLEMIZED_CLASS_NS
try:
    from rdflib.graph import Graph
except ImportError:
    from rdflib.Graph import Graph
from rdflib import Namespace

EX = Namespace('http://example.com#')

class UnionSkolemizedTest(unittest.TestCase):
    def setUp(self):
        self.tBoxGraph=Graph()
        self.tBoxGraph.namespace_manager.bind('ex',EX)
        self.tBoxGraph.namespace_manager.bind('owl',OWL_NS)
        Individual.factoryGraph = self.tBoxGraph
        self.classB = Class(EX.b)
        self.classE = Class(EX.e)
        self.classF = Class(EX.f) 
        self.classA = BooleanClass(EX.a,
                                   operator=OWL_NS.unionOf,
                                   members=[self.classE,self.classF])
        self.classC = BooleanClass(EX.c,
                                   operator=OWL_NS.unionOf,
                                   members=[self.classA,self.classB])
        self.ruleStore,self.ruleGraph=SetupRuleStore()

    def testUnionSkolemization(self):
        network = ReteNetwork(self.ruleStore) #,nsMap = self.ruleStore.nsMgr)
        p = network.setupDescriptionLogicProgramming(self.tBoxGraph)
        for p in p:
            self.failIf(p.formula.body.arg[-1].find(SKOLEMIZED_CLASS_NS) >- 1,
                        "Rule has a skolem term when it shouldn't!: %s"%p)
    
if __name__ == '__main__':
    unittest.main()