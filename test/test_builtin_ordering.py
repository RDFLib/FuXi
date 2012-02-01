#!/usr/bin/env python
import unittest
from pprint import pprint
from cStringIO import StringIO
try:
    from rdflib.graph import Graph, ConjunctiveGraph, QuotedGraph
except ImportError:
    from rdflib.Graph import Graph, QuotedGraph, ConjunctiveGraph
from rdflib import Literal, Variable, URIRef, Namespace
from FuXi.Rete.BuiltinPredicates import FILTERS, STRING_NS
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.Horn.HornRules import HornFromN3, NetworkFromN3
from FuXi.Rete.BuiltinPredicates import FILTERS, STRING_NS

TEST_NS = Namespace("http://example.org/test#")
LOG = Namespace("http://www.w3.org/2000/10/swap/log#")

def StringStartsWith(subject, object_):
    for term in (subject, object_):
        assert isinstance(term, (Variable, Literal, URIRef)), \
            "str:startsWith terms must be Variables, Literals, or URIRefs!"
    def startsWithF(subject_value, object_value):
        return subject_value.startswith(object_value)
    return startsWithF

def extractBaseFacts(cg):
    """
    Takes a conjunctive graph and returns
    a generator of RDF facts (excluding N3 facts
    involving log:implies and triples in QuotedGraphs)
    """
    for ctx in cg.contexts():
        if not isinstance(ctx,QuotedGraph):
            for s,p,o in ctx:
                if p != LOG.implies:
                    yield s,p,o

def build_network(rules):
    if isinstance(rules, basestring):
        rules = StringIO(rules)
    graph = ConjunctiveGraph()
    graph.load(rules, publicID='test', format='n3')
    network = NetworkFromN3(graph,
                            additionalBuiltins={STRING_NS.startsWith:StringStartsWith})
    network.feedFactsToAdd(generateTokenSet(extractBaseFacts(graph)))
    return network

def build_network2(rules):
    graph = ConjunctiveGraph()
    graph.load(StringIO(rules), publicID='test', format='n3')    
    rule_store, rule_graph=SetupRuleStore(
                      StringIO(rules),
                      additionalBuiltins={STRING_NS.startsWith:StringStartsWith})
    from FuXi.Rete.Network import ReteNetwork
    network = ReteNetwork(rule_store)
    network.feedFactsToAdd(generateTokenSet(extractBaseFacts(graph)))
    return network

class LiteralStringStartsWith(unittest.TestCase):
    fact = (TEST_NS.test, TEST_NS.passes, Literal(1))
    rules = """
    @prefix test: <http://example.org/test#> .
    @prefix str: <http://www.w3.org/2000/10/swap/string#> .

    test:example test:value "example" .
    { test:example test:value ?value .
      ?value str:startsWith "ex" } => { test:test test:passes 1 } .
    """
    def setUp(self):
        self.network  = build_network(self.rules)
        self.network2 = build_network2(self.rules)

    def test_literal_variable_startswith_literal_should_match(self):
        self.failUnless(self.fact in self.network.inferredFacts)
    def test_literal_variable_startswith_literal_should_match2(self):        
        self.failUnless(self.fact in self.network2.inferredFacts)

class URIRefStringStartsWith(unittest.TestCase):
    fact = (TEST_NS.test, TEST_NS.passes, Literal(1))
    rules = """
    @prefix test: <http://example.org/test#> .
    @prefix str: <http://www.w3.org/2000/10/swap/string#> .

    test:example test:value test:example .
    { test:example test:value ?value .
      ?value str:startsWith "http://example.org/test#ex" } => { test:test test:passes 1 } .
    """
    def setUp(self):
        self.network  = build_network(self.rules)
        self.network2 = build_network2(self.rules)

    def test_uriref_variable_startswith_literal_should_match(self):
        self.failUnless(self.fact in self.network.inferredFacts)
    def test_uriref_variable_startswith_literal_should_match2(self):        
        self.failUnless(self.fact in self.network2.inferredFacts)

if __name__ == '__main__':
    unittest.main()
