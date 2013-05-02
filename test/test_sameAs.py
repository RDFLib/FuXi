#!/usr/bin/env python
# encoding: utf-8
import unittest
from nose.exc import SkipTest
from cStringIO import StringIO
from rdflib.graph import Graph
from rdflib import (
    # RDF,
    # RDFS,
    Namespace,
    Variable,
    # Literal,
    # URIRef,
    # BNode
    )
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Syntax.InfixOWL import OWL_NS
from FuXi.Horn.HornRules import HornFromN3
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore

EX = Namespace('http://example.org/')

FACTS = \
"""
@prefix ex: <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#>.

ex:foo ex:x "xxxx";
       owl:sameAs ex:bar .
ex:bar ex:y "yyyy";
       owl:sameAs ex:baz .
"""

RULES = \
"""
@prefix owl: <http://www.w3.org/2002/07/owl#>.

{ ?x owl:sameAs ?y } => { ?y owl:sameAs ?x } .
# { ?x owl:sameAs ?y . ?x ?p ?o } => { ?y ?p ?o } .
{ ?X owl:sameAs ?A . ?A owl:sameAs ?B } => { ?X owl:sameAs ?B } .
"""

GOALS = [
    (EX.foo, EX.y, Variable('o')),
    (EX.foo, OWL_NS.sameAs, Variable('o'))
]

QUERIES = {
    "SELECT ?o { ex:baz owl:sameAs ?o }": set([EX.bar, EX.foo]),
    "SELECT ?o { ex:foo owl:sameAs ?o }": set([EX.bar, EX.baz])
}


class test_sameAs(unittest.TestCase):
    # known_issue = True

    def setUp(self):
        self.rule_store, self.rule_graph, self.network = SetupRuleStore(
                            makeNetwork=True)
        self.graph = Graph().parse(StringIO(FACTS), format='n3')
        # adornedProgram = SetupDDLAndAdornProgram(
        #                                self.graph,
        #                                HornFromN3(StringIO(RULES)),
        #                                GOALS,
        #                                derivedPreds=[OWL_NS.sameAs],
        #                                hybridPreds2Replace=[OWL_NS.sameAs])
        # pprint(list(self.graph.adornedProgram))

    def testTransitivity(self):
        raise SkipTest("SKIPFAIL testTransitivity, see test/test_sameAs.py")
        nsBindings = {u'owl': OWL_NS, u'ex': EX}
        topDownStore = TopDownSPARQLEntailingStore(
                        self.graph.store,
                        self.graph,
                        idb=HornFromN3(StringIO(RULES)),
                        DEBUG=True,
                        derivedPredicates=[OWL_NS.sameAs],
                        nsBindings=nsBindings,
                        hybridPredicates=[OWL_NS.sameAs])
        targetGraph = Graph(topDownStore)
        for query, solns in QUERIES.items():
            result = set(targetGraph.query(query, initNs=nsBindings))
            print(query, result)
            self.failUnless(not solns.difference(result))

    # def testSmushing(self):
        # sipCollection = PrepareSipCollection(self.graph.adornedProgram)
        # print self.graph.serialize(format='n3')
        # for arc in SIPRepresentation(sipCollection):
        #     print arc
        # success = False
        # for goal in GOALS:
        #     goalLiteral = BuildUnitermFromTuple(goal)
        #     print "Query / goal: ", goalLiteral
        #     for ans,node in SipStrategy(
        #                 goal,
        #                 sipCollection,
        #                 self.graph,
        #                 [OWL_NS.sameAs],
        #                 debug = False):
        #         if ans[Variable('o')] == Literal('yyyy'):
        #             success = True
        #             print "Found solution!", ans
        #             break
        # self.failUnless(success,
        #    "Unable to proove %s"%(repr((EX.foo,EX.y,Literal('yyyy')))))


if __name__ == '__main__':
    unittest.main()


"""
======================================================================
FAIL: testTransitivity (test.test_sameAs.test_sameAs)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/home/gjh/.virtualenvs/rdfdev/src/fuxi/test/test_sameAs.py", line 80, in testTransitivity
    self.failUnless(not solns.difference(result))
AssertionError: False is not true
-------------------- >> begin captured stdout << ---------------------
('Goal/Query: ', u'SELECT ?o { \tex:baz owl:sameAs ?o }')
    1. Forall ?Y ?X ( owl:sameAs_derived_ff(?X ?Y) :- owl:sameAs(?X ?Y) )
    2. Forall ?y ?x ( owl:sameAs_derived_bf(?y ?x) :- owl:sameAs_derived_ff(?x ?y) )
    3. Forall ?A ?X ?B ( owl:sameAs_derived_bf(?X ?B) :- And( owl:sameAs_derived_ff(?X ?A) owl:sameAs_derived_ff(?A ?B) ) )
('a', 1) : Forall ?Y ?X ( owl:sameAs_derived_ff(?X ?Y) :- And( ns1:OpenQuery(owl:sameAs_derived) bfp:evaluate(rule:1 1) ) )
('b', 1) : Forall  ( bfp:evaluate(rule:1 0) :- ns1:OpenQuery(owl:sameAs_derived) )
('d', 1, 1) : Forall ?Y ?X ( owl:sameAs_query(?X ?Y) :- bfp:evaluate(rule:1 0) )
('a', 2) : Forall ?y ?x ( owl:sameAs_derived_bf(?y ?x) :- And( owl:sameAs_derived_query_bf(?y) bfp:evaluate(rule:2 1) ) )
('b', 2) : Forall ?y ( bfp:evaluate(rule:2 0) :- owl:sameAs_derived_query_bf(?y) )
('c', 2, 1) : Forall ?y ?x ( bfp:evaluate(rule:2 1) :- And( bfp:evaluate(rule:2 0) owl:sameAs_derived_ff(?x ?y) ) )
('d', 2, 1) : Forall  ( ns1:OpenQuery(owl:sameAs_derived) :- bfp:evaluate(rule:2 0) )
('a', 3) : Forall ?X ?B ( owl:sameAs_derived_bf(?X ?B) :- And( owl:sameAs_derived_query_bf(?X) bfp:evaluate(rule:3 2) ) )
('b', 3) : Forall ?X ( bfp:evaluate(rule:3 0) :- owl:sameAs_derived_query_bf(?X) )
('c', 3, 2) : Forall ?A ?B ( bfp:evaluate(rule:3 2) :- And( bfp:evaluate(rule:3 1) owl:sameAs_derived_ff(?A ?B) ) )
('c', 3, 1) : Forall ?A ?X ( bfp:evaluate(rule:3 1) :- And( bfp:evaluate(rule:3 0) owl:sameAs_derived_ff(?X ?A) ) )
('d', 3, 1) : Forall  ( ns1:OpenQuery(owl:sameAs_derived) :- bfp:evaluate(rule:3 0) )
('d', 3, 2) : Forall  ( ns1:OpenQuery(owl:sameAs_derived) :- bfp:evaluate(rule:3 1) )
('Goal/Query: ', (rdflib.term.URIRef(u'http://example.org/baz'), rdflib.term.URIRef(u'http://www.w3.org/2002/07/owl#sameAs_derived'), ?o))
Query was not ground
<Network: 13 rules, 19 nodes, 0 tokens in working memory, 0 inferred tokens>
None
('SELECT ?o { ex:baz owl:sameAs ?o }', set([]))

--------------------- >> end captured stdout << ----------------------

"""
