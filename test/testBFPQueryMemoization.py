import unittest
from nose.exc import SkipTest
from cStringIO import StringIO
from rdflib.graph import Graph
from rdflib import (
    RDF,
    # RDFS,
    Namespace,
    Variable,
    URIRef
    )
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.SPARQL.BackwardChainingStore import *
from FuXi.Syntax.InfixOWL import *

EX_ONT = \
"""
@prefix first: <http://www.w3.org/2002/03owlt/intersectionOf/premises001#>.
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.

 first:C owl:intersectionOf ( first:Employee first:Student ).

 first:John a first:B.

 first:B owl:intersectionOf ( first:Student first:Employee ).

"""

EX = Namespace('http://www.w3.org/2002/03owlt/intersectionOf/premises001#')

nsMap = {
u'owl': OWL_NS,
u'first': URIRef('http://www.w3.org/2002/03owlt/intersectionOf/premises001#'),
}


class QueryCountingGraph(Graph):
    def __init__(self, store='default', identifier=None,
                     namespace_manager=None):
        self.queriesDispatched = []
        super(QueryCountingGraph, self).__init__(
                store, identifier, namespace_manager)

    def query(self, strOrQuery, initBindings={}, initNs={}, DEBUG=False,
              PARSE_DEBUG=False,
              dataSetBase=None,
              processor="sparql",
              extensionFunctions={},
              parsedQuery=None):
        self.queriesDispatched.append(strOrQuery)
        return super(QueryCountingGraph, self).query(strOrQuery,
                                                     initBindings=initBindings,
                                                     initNs=initNs,
                                                     processor=processor,
                                                     use_store_provided=False,
                                                     DEBUG=True,
                                                     #PARSE_DEBUG,
                                                     #dataSetBase,
                                                     #extensionFunctions,
                                                     #parsedQuery
                                                     )


class QueryMemoizationTest(unittest.TestCase):
    def setUp(self):
        self.owlGraph = QueryCountingGraph().parse(
                            StringIO(EX_ONT), format='n3')
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.program = self.network.setupDescriptionLogicProgramming(
                                                     self.owlGraph,
                                                     addPDSemantics=False,
                                                     constructNetwork=False)
        self.program.update(AdditionalRules(self.owlGraph))

    def testQueryMemoization(self):
        raise SkipTest("SKIPFAIL testQueryMemoization, see test/testBFPQueryMemoization.py")
        topDownStore = TopDownSPARQLEntailingStore(
                        self.owlGraph.store,
                        self.owlGraph,
                        idb=self.program,
                        DEBUG=False,
                        nsBindings=nsMap,
                        decisionProcedure=BFP_METHOD,
                        identifyHybridPredicates=True)
        targetGraph = Graph(topDownStore)
        for pref, nsUri in nsMap.items():
            targetGraph.bind(pref, nsUri)
        goal = (Variable('SUBJECT'), RDF.type, EX.C)
        queryLiteral = EDBQuery([BuildUnitermFromTuple(goal)],
                                self.owlGraph,
                                [Variable('SUBJECT')])
        query = queryLiteral.asSPARQL()
        # rt=targetGraph.query(query,initNs=nsMap)
        # if len(topDownStore.edbQueries) == len(set(topDownStore.edbQueries)):
        #     pprint(topDownStore.edbQueries)
        print("Queries dispatched against EDB")
        for query in self.owlGraph.queriesDispatched:
            print(query)
        self.failUnlessEqual(
            len(self.owlGraph.queriesDispatched), 4, "Duplicate query")


if __name__ == "__main__":
    unittest.main()

"""
======================================================================
FAIL: testQueryMemoization (test.testBFPQueryMemoization.QueryMemoizationTest)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/home/gjh/.virtualenvs/rdfdev/src/fuxi/test/testBFPQueryMemoization.py", line 100, in testQueryMemoization
    len(self.owlGraph.queriesDispatched), 4, "Duplicate query")
AssertionError: Duplicate query
-------------------- >> begin captured stdout << ---------------------
createSPARQLPConstraint reducedFilter=<ConditionalExpressionList: [(KIND = owl:InverseFunctionalProperty), (KIND = owl:FunctionalProperty)]>, type=<class 'rdfextras.sparql.components.ParsedConditionalAndExpressionList'>
createSPARQLPConst: reducedFilterType = <class 'rdfextras.sparql.components.ParsedConditionalAndExpressionList'>, constraint = False
mapToOperator:
    expr=(KIND = owl:InverseFunctionalProperty),
    type=<class 'rdfextras.sparql.components.EqualityOperator'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [?KIND]>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [u'owl:InverseFunctionalProperty']>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=(KIND = owl:FunctionalProperty),
    type=<class 'rdfextras.sparql.components.EqualityOperator'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [?KIND]>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [u'owl:FunctionalProperty']>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

a. sparql-p operator(s): lambda i: operators.eq("?KIND",'http://www.w3.org/2002/07/owl#InverseFunctionalProperty')(i) or operators.eq("?KIND",'http://www.w3.org/2002/07/owl#FunctionalProperty')(i)
createSPARQLPConstraint reducedFilter=<ConditionalExpressionList: [(KIND = owl:InverseFunctionalProperty), (KIND = owl:FunctionalProperty)]>, type=<class 'rdfextras.sparql.components.ParsedConditionalAndExpressionList'>
createSPARQLPConst: reducedFilterType = <class 'rdfextras.sparql.components.ParsedConditionalAndExpressionList'>, constraint = False
mapToOperator:
    expr=(KIND = owl:InverseFunctionalProperty),
    type=<class 'rdfextras.sparql.components.EqualityOperator'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [?KIND]>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [u'owl:InverseFunctionalProperty']>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=(KIND = owl:FunctionalProperty),
    type=<class 'rdfextras.sparql.components.EqualityOperator'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [?KIND]>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

mapToOperator:
    expr=<AdditiveExpressionList: [<MultiplicativeExpressionList: [u'owl:FunctionalProperty']>]>,
    type=<class 'rdfextras.sparql.components.ParsedAdditiveExpressionList'>,
    constr=False.

a. sparql-p operator(s): lambda i: operators.eq("?KIND",'http://www.w3.org/2002/07/owl#InverseFunctionalProperty')(i) or operators.eq("?KIND",'http://www.w3.org/2002/07/owl#FunctionalProperty')(i)
Queries dispatched against EDB

ASK {
  [] a ?KIND
  FILTER(
      ?KIND = owl:InverseFunctionalProperty ||
      ?KIND = owl:FunctionalProperty
  )
}

ASK {
  [] a ?KIND
  FILTER(
      ?KIND = owl:InverseFunctionalProperty ||
      ?KIND = owl:FunctionalProperty
  )
}

--------------------- >> end captured stdout << ----------------------
-------------------- >> begin captured logging << --------------------
rdfextras.sparql.algebra: DEBUG: ## Full SPARQL Algebra expression ##
rdfextras.sparql.algebra: DEBUG: Filter(.. a filter ..,BGP(_:Neb4be2109f58434fb9b776fe285f4a4d,rdf:type,?KIND))
rdfextras.sparql.algebra: DEBUG: ###################################
rdfextras.sparql.algebra: DEBUG: ## Full SPARQL Algebra expression ##
rdfextras.sparql.algebra: DEBUG: Filter(.. a filter ..,BGP(_:Nc1882a8aed2941c6abad2c1bc9a51bdb,rdf:type,?KIND))
rdfextras.sparql.algebra: DEBUG: ###################################
--------------------- >> end captured logging << ---------------------

"""
