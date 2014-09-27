# -*- coding: utf-8 -*-
import unittest
from cStringIO import StringIO
from rdflib import Graph, Literal, Namespace, Variable
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.Util import generateTokenSet
from FuXi.Rete.RuleStore import SetupRuleStore
FOAF = Namespace('http://xmlns.com/foaf/0.1/')
EX = Namespace('http://example.com/#')

N3_PROGRAM = \
"""
@prefix m: <http://example.com/#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/> .

{ ?person m:name ?name } => { ?person foaf:name ?name } ."""

N3_FACTS = \
"""
@prefix m: <http://example.com/#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/> .

m:ross m:name "Ross"@en .
m:ross m:name "Ross"@de .
m:ross m:name "呂好"@ja .
"""

resulting_triples = [
    (EX.ross, FOAF['name'], Literal('Ross', lang='en')),
    (EX.ross, FOAF['name'], Literal('Ross', lang='de')),
    (EX.ross, FOAF['name'], Literal('呂好', lang='ja'))
]


class ReteMultiLangTest(unittest.TestCase):
    def test_multi_lang_inference(self):

        graph = Graph().parse(StringIO(N3_FACTS), format='n3')
        rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)

        for rule in HornFromN3(StringIO(N3_PROGRAM), additionalBuiltins=None):
            network.buildNetworkFromClause(rule)

        network.feedFactsToAdd(generateTokenSet(graph))

        for expected_triple in resulting_triples:
            self.assertIn(expected_triple, network.inferredFacts)


if __name__ == "__main__":
    unittest.main()
