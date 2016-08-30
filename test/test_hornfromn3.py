#!/usr/bin/env python
# encoding: utf-8
import unittest
from rdflib import Graph
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.RuleStore import SetupRuleStore, N3RuleStore
from FuXi.Rete.Util import generateTokenSet
from rdflib import Graph


src = u"""\
@prefix : <http://metacognition.info/FuXi/test#>.
@prefix str:   <http://www.w3.org/2000/10/swap/string#>.
@prefix math: <http://www.w3.org/2000/10/swap/math#>.
@prefix log:   <http://www.w3.org/2000/10/swap/log#>.
@prefix m: <http://metacognition.info/FuXi/test#>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix owl: <http://www.w3.org/2002/07/owl#>.
m:a a rdfs:Class;
   m:prop1 1;
   m:prop2 4.
m:b a owl:Class;
   m:prop1 2;
   m:prop2 4, 1, 5.
(1 2) :relatedTo (3 4).
{ ?X a owl:Class. ?X :prop1 ?M. ?X :prop2 ?N. ?N math:equalTo 3 } => { [] :selected (?M ?N) }."""

rules = u"""\
@prefix owl: <http://www.w3.org/2002/07/owl#> .
{ ?x owl:sameAs ?y } => { ?y owl:sameAs ?x } .
{ ?x owl:sameAs ?y . ?x ?p ?o } => { ?y ?p ?o } .
"""

facts = u"""\
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix ex: <http://example.org/> .
@prefix trms: <http://example.org/terms/> .
ex:foo
        a trms:Something ;
        trms:hasX "blah blah" ;
        owl:sameAs ex:bar .
ex:bar
        trms:hasY "yyyy" ."""


class TestHornFromN3(unittest.TestCase):
    """Test HornFromN3 on http://www.agfa.com/w3c/euler/rdfs-rules.n3."""

    def setUp(self):
        pass

    def test_issue_13(self):
        """Test issue 13.

        https://github.com/RDFLib/FuXi/issues/13
        """
        rules = HornFromN3(
            'http://www.agfa.com/w3c/euler/rdfs-rules.n3')
        for rule in rules:
            assert 'And(  )' not in str(rule), str(rule)

    def test_hornfromn3(self):
        self.rule_store, self.rule_graph, self.network = SetupRuleStore(
            makeNetwork=True)
        closureDeltaGraph = Graph()
        self.network.inferredFacts = closureDeltaGraph
        for rule in HornFromN3(
                'http://www.agfa.com/w3c/euler/rdfs-rules.n3',
                additionalBuiltins=None):
            self.network.buildNetworkFromClause(rule)
            print("{} {}".format(self.network, rule))
            # state_before_inferencing = str(self.network)
            self.network.feedFactsToAdd(generateTokenSet(self.network.inferredFacts))
            # state_after_inferencing = str(self.network)
            # assert state_before_inferencing != state_after_inferencing, str(self.network)

    def test_n3rulestore_basic(self):
        s = N3RuleStore()
        g = Graph(s)
        g.parse(data=src, format='n3')
        s._finalize()
        assert len([pred for subj, pred, obj in s.facts if pred == 'http://metacognition.info/FuXi/test#relatedTo']) == 1, len([pred for subj, pred, obj in s.facts if pred == 'http://metacognition.info/FuXi/test#relatedTo'])
        assert len(s.rules) == 1, len(s.rules)
        assert len(s.rules[0][RULE_LHS]) == 4, len(s.rules[0][RULE_LHS])
        assert len(s.rules[0][RULE_RHS]) == 5, len(s.rules[0][RULE_RHS])
        assert s.rules[0][RULE_LHS][1] == "(rdflib.term.Variable('X'), rdflib.term.URIRef('http://metacognition.info/FuXi/test#prop1'), rdflib.term.Variable('M'))", s.rules[0][RULE_LHS][1]
        assert s.rules[0][RULE_LHS][-1] == "<http://www.w3.org/2000/10/swap/math#equalTo>(?N, 3)", s.rules[0][RULE_LHS][-1]

    def test_hornfromn3_inferencing(self):
        # https://groups.google.com/d/msg/fuxi-discussion/4r1Nt_o1Hco/4QQ7BaqBCH8J
        from io import StringIO
        rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
        for rule in HornFromN3(StringIO(rules)):
            network.buildNetworkFromClause(rule)
        g = Graph()
        g.parse(data=facts, format="n3")
        network.feedFactsToAdd(generateTokenSet(g))
        print(network.inferredFacts.serialize(format="n3").decode('utf-8'))

if __name__ == '__main__':
    unittest.main()
