import unittest
from cStringIO import StringIO
try:
    from rdflib.graph import Graph
except ImportError:
    from rdflib.Graph import Graph
from rdflib import RDF, RDFS, Namespace, Variable, URIRef
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
  u'owl'  :OWL_NS,
  u'first':URIRef('http://www.w3.org/2002/03owlt/intersectionOf/premises001#'),
}

class QueryCountingGraph(Graph):
    def __init__(self, store='default', identifier=None,
                     namespace_manager=None):
        self.queriesDispatched = []
        super(QueryCountingGraph, self).__init__(store,identifier,namespace_manager)

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
                                                     #DEBUG,
                                                     #PARSE_DEBUG,
                                                     #dataSetBase,
                                                     #extensionFunctions,
                                                     #parsedQuery
                                                     )
class QueryMemoizationTest(unittest.TestCase):
    def setUp(self):
        self.owlGraph = QueryCountingGraph().parse(StringIO(EX_ONT),format='n3')
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.program = self.network.setupDescriptionLogicProgramming(
                                                     self.owlGraph,
                                                     addPDSemantics=False,
                                                     constructNetwork=False)
        self.program.update(AdditionalRules(self.owlGraph))

    def testQueryMemoization(self):
        topDownStore=TopDownSPARQLEntailingStore(
                        self.owlGraph.store,
                        self.owlGraph,
                        idb=self.program,
                        DEBUG=False,
                        nsBindings=nsMap,
                        decisionProcedure = BFP_METHOD,
                        identifyHybridPredicates = True)
        targetGraph = Graph(topDownStore)
        for pref,nsUri in nsMap.items():
            targetGraph.bind(pref,nsUri)
        goal = (Variable('SUBJECT'),RDF.type,EX.C)
        queryLiteral = EDBQuery([BuildUnitermFromTuple(goal)],
                                self.owlGraph,
                                [Variable('SUBJECT')])
        query = queryLiteral.asSPARQL()
        # rt=targetGraph.query(query,initNs=nsMap)
#        if len(topDownStore.edbQueries) == len(set(topDownStore.edbQueries)):
#            pprint(topDownStore.edbQueries)
        print "Queries dispatched against EDB"
        for query in self.owlGraph.queriesDispatched:
            print query
        self.failUnlessEqual(len(self.owlGraph.queriesDispatched),4,"Duplicate query")
if __name__ == "__main__":
    unittest.main()