import unittest
from cStringIO import StringIO
from rdflib import Graph, Literal, Namespace, Variable
try:
    from rdflib.graph import Graph
except ImportError:
    from rdflib.Graph import Graph
from rdflib import RDF, RDFS, Namespace, Variable, Literal, URIRef, BNode
from rdflib.util import first
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.Util import generateTokenSet
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Horn.PositiveConditions import GetUterm
FOAF = Namespace('http://xmlns.com/foaf/0.1/')
EX   = Namespace('http://example.com/#')

N3_PROGRAM=\
"""
@prefix m: <http://example.com/#>.
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .

{ ?person foaf:mbox ?email } => { ?person foaf:mbox_sha1sum rdf:Literal } ."""
N3_FACTS=\
"""
@prefix m: <http://example.com/#>.
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .

m:chimezie foaf:mbox <mailto:chimezie@example.com> .
"""

matchingHeadTriple = (Variable('person'),
                      FOAF['mbox_sha1sum'],
                      Literal)
resultingTriple = (EX.chimezie,FOAF['mbox_sha1sum'],Literal('8f90d9335f967f58b40d5b6a49f8d9afca64b5ae'))

def encodeAction(tNode, inferredTriple, token, binding, debug = False):
  from hashlib import sha1
  person = binding[Variable('person')]
  email = binding[Variable('email')]
  newTriple = (person,FOAF['mbox_sha1sum'],Literal(sha1(email).hexdigest()))
  tNode.network.inferredFacts.add(newTriple)

class ReteActionTest(unittest.TestCase):
    def testReteActionTest(self):
        factGraph = Graph().parse(StringIO(N3_FACTS),format='n3')
        rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
        for rule in HornFromN3(StringIO(N3_PROGRAM),additionalBuiltins=None):
            network.buildNetworkFromClause(rule)
        network.registerReteAction(matchingHeadTriple,False,encodeAction)
        network.feedFactsToAdd(generateTokenSet(factGraph))
        print network.inferredFacts.serialize(format='n3')
        self.failUnless(resultingTriple in network.inferredFacts)

if __name__ == "__main__":
    unittest.main()
