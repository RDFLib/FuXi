#!/usr/bin/env python
# encoding: utf-8
import unittest
from cStringIO import StringIO
from rdflib.graph import Graph
from rdflib import Namespace, Variable
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
    def setUp(self):
        self.rule_store, self.rule_graph, self.network = \
                                SetupRuleStore(makeNetwork=True)
        self.graph = Graph().parse(StringIO(FACTS), format='n3')
        # adornedProgram = SetupDDLAndAdornProgram(
        #                                self.graph,
        #                                HornFromN3(StringIO(RULES)),
        #                                GOALS,
        #                                derivedPreds=[OWL_NS.sameAs],
        #                                hybridPreds2Replace=[OWL_NS.sameAs])
        # pprint(list(self.graph.adornedProgram))

    def testTransitivity(self):
        # from nose.exc import SkipTest
        # raise SkipTest("fails with Exception in SidewaysInformationPassing")
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
        # self.failUnless(success,"Unable to proove %s" % (
        #                   repr((EX.foo, EX.y, Literal('yyyy')))))

if __name__ == '__main__':
    unittest.main()

"""
testTransitivity failure:

======================================================================
ERROR: testTransitivity (test_sameAs.test_sameAs)
----------------------------------------------------------------------
Traceback (most recent call last):
  File ".../fuxi/test/test_sameAs.py", line 70, in testTransitivity
    result = set(targetGraph.query(query, initNs=nsBindings))
  File ".../rdflib/graph.py", line 938, in query
    return result(processorinst.query(query_object, initBindings, initNs, **kwargs))
  File ".../rdfextras/sparql/processor.py", line 49, in query
    loadContexts=loadContexts)
  File ".../rdfextras/sparql/algebra.py", line 388, in TopEvaluate
    top.topLevelExpand(expr.constraints, query.prolog)
  File ".../rdfextras/sparql/query.py", line 520, in topLevelExpand
    self.expand(constraints)
  File ".../rdfextras/sparql/query.py", line 593, in expand
    for rtDict in self.tripleStore.graph.store.batch_unify(patterns):
  File ".../fuxi/FuXi/SPARQL/BackwardChainingStore.py", line 452, in batch_unify
    self.edb):
  File ".../fuxi/FuXi/SPARQL/BackwardChainingStore.py", line 293, in conjunctiveSipStrategy
    ignoreUnboundDPreds = True)
  File ".../fuxi/FuXi/Rete/Magic.py", line 106, in SetupDDLAndAdornProgram
    hybridPreds2Replace = hybridPreds2Replace)
  File ".../fuxi/FuXi/Rete/Magic.py", line 458, in AdornProgram
    hybridPreds2Replace = hybridPreds2Replace)
  File ".../fuxi/FuXi/Rete/Magic.py", line 347, in AdornRule
    op   = GetOp(literal)
  File ".../fuxi/FuXi/Rete/SidewaysInformationPassing.py", line 156, in GetOp
    raise Exception('''GetOp unable to get op of "%s"''' % term)
Exception: GetOp unable to get op of "And(  )"
-------------------- >> begin captured stdout << ---------------------
Hybrid predicates:  [rdflib.term.URIRef(u'http://www.w3.org/2002/07/owl#sameAs')]

--------------------- >> end captured stdout << ----------------------
"""
