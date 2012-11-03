import unittest
from cStringIO import StringIO
from rdflib.graph import Graph
from rdflib import RDF, Namespace, Variable, URIRef
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.SPARQL.BackwardChainingStore import BFP_METHOD
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from FuXi.Syntax.InfixOWL import OWL_NS
from FuXi.SPARQL import EDBQuery
from FuXi.Horn.PositiveConditions import BuildUnitermFromTuple
import logging


def _debug(*args, **kw):
    logging.basicConfig(level=logging.ERROR, format="%(message)s")
    logger = logging.getLogger(__name__)
    logger.setLevel(logging.DEBUG)
    logger.debug(*args, **kw)


EX_ONT = \
u"""
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
  u'first':
    URIRef('http://www.w3.org/2002/03owlt/intersectionOf/premises001#'),
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
                                                     #DEBUG,
                                                     #PARSE_DEBUG,
                                                     #dataSetBase,
                                                     #extensionFunctions,
                                                     #parsedQuery
                                                     )


class QueryMemoizationTest(unittest.TestCase):
    def setUp(self):
        self.owlGraph = QueryCountingGraph().parse(data=EX_ONT, format='n3')
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.program = self.network.setupDescriptionLogicProgramming(
                                                     self.owlGraph,
                                                     addPDSemantics=False,
                                                     constructNetwork=False)
        self.program.update(AdditionalRules(self.owlGraph))

    # def testQueryMemoization(self):
    #     topDownStore = TopDownSPARQLEntailingStore(
    #                     self.owlGraph.store,
    #                     self.owlGraph,
    #                     idb=self.program,
    #                     DEBUG=False,
    #                     nsBindings=nsMap,
    #                     decisionProcedure=BFP_METHOD,
    #                     identifyHybridPredicates=True)
    #     targetGraph = Graph(topDownStore)
    #     for pref, nsUri in nsMap.items():
    #         targetGraph.bind(pref, nsUri)
    #     _debug("Queries dispatched against EDB")
    #     # print("# queries {}".format(len(self.owlGraph.queriesDispatched)))
    #     # self.assertEqual(len(self.owlGraph.queriesDispatched), 4)
    #     assert len(self.owlGraph.queriesDispatched) == 4

    def testQueryMemoization(self):
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
        rt = targetGraph.query(query, initNs=nsMap)
        # if len(topDownStore.edbQueries) == len(set(topDownStore.edbQueries)):
        #     pprint(topDownStore.edbQueries)
        _debug("Queries dispatched against EDB")
        for query in self.owlGraph.queriesDispatched:
            _debug(query)
        self.failUnlessEqual(
            len(self.owlGraph.queriesDispatched), 4, "Duplicate query")

if __name__ == "__main__":
    unittest.main()
