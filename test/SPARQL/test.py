"""
FuXi Harness for W3C SPARQL1.1 Entailment Evaluation Tests
"""

import unittest
from pprint import pprint
from urllib2 import urlopen
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.Proof import ImmutableDict
from FuXi.SPARQL.BackwardChainingStore import *
from FuXi.Rete.Util import setdict

from rdflib import Namespace, RDF, RDFS, URIRef
try:
    from rdflib import BNode, Graph, Literal, Namespace, RDF, RDFS, URIRef, Variable
    from rdfextras.sparql.parser import parse
    from rdflib import OWL as OWLNS
except ImportError:
    from rdflib.Namespace import Namespace
    from rdflib import BNode, Graph, Literal, RDF, RDFS, URIRef, Variable
    from rdflib.sparql.parser import parse
    from rdflib import OWL
    OWLNS = str(OWL.OWLNS)
    RDF = str(RDF.RDFNS)
    RDFS = str(RDFS.RDFSNS)
from rdflib.store import Store


from amara.lib import U

MANIFEST  = Namespace('http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#')
QUERY     = Namespace('http://www.w3.org/2001/sw/DataAccess/tests/test-query#')
SD        = Namespace('http://www.w3.org/ns/sparql-service-description#')
TEST      = Namespace('http://www.w3.org/2009/sparql/docs/tests/data-sparql11/entailment/manifest#')
STRING    = Namespace('http://www.w3.org/2000/10/swap/string#')
ENT       = Namespace('http://www.w3.org/ns/entailment/')

SUPPORTED_ENTAILMENT=[
    ENT.RDF,
    ENT.RDFS
]

SKIP={
    "rdf01" : "Quantification over predicates",
    "rdfs01": "Quantification over predicates",
    "rdf02" : "Reification",
    "rdf10" : "Malformed test", #might be fixed
    "rdfs05": "Quantification over predicates (unary)",
    "rdfs11": "Reflexivity of rdfs:subClassOf (?x -> rdfs:Container)"
}

nsMap = {
  u'rdfs' :RDFS,
  u'rdf'  :RDF,
  u'owl'  :OWLNS,
  u'mf'   :MANIFEST,
  u'sd'   :SD,
  u'test' :MANIFEST,
  u'qt'   :QUERY
}
MANIFEST_QUERY = \
"""
SELECT ?test ?name ?queryFile ?rdfDoc ?regime ?result
WHERE {
  ?test
    a test:QueryEvaluationTest;
      mf:name ?name;
      mf:action [
        qt:query ?queryFile;
        qt:data  ?rdfDoc;
        sd:entailmentRegime ?regime
      ];
      mf:result ?result
} ORDER BY ?test """

def GetTests():
    manifestGraph = Graph().parse(
        open('SPARQL/W3C/entailment/manifest.ttl'),
        format='n3')
    rt = manifestGraph.query(
                              MANIFEST_QUERY,
                              initNs=nsMap,
                              DEBUG = False)
    for test, name, queryFile, rdfDoc, regime, result in rt:
        yield test.split(TEST)[-1], \
              name, \
              queryFile, \
              rdfDoc, \
              regime, \
              result

def castToTerm(node):
    if node.xml_local == 'bnode':
        return BNode(U(node))
    elif node.xml_local == 'uri':
        return URIRef(U(node))
    elif node.xml_local == 'literal':
        if node.xml_select('string(@datatype)'):
            dT = URIRef(U(node.xpath('string(@datatype)')))
            return Literal(U(node),datatype=dT)
        else:
            return Literal(U(node))
    else:
        raise NotImplementedError()

def parseResults(sparqlRT):
    from amara import bindery
    actualRT = []
    doc = bindery.parse(sparqlRT,
                        prefixes={
                            u'sparql':u'http://www.w3.org/2005/sparql-results#'})
    askAnswer=doc.xml_select('string(/sparql:sparql/sparql:boolean)')
    if askAnswer:
        askAnswer = U(askAnswer)
        actualRT=askAnswer==u'true'
    else:
        for result in doc.xml_select('/sparql:sparql/sparql:results/sparql:result'):
            currBind = {}
            for binding in result.binding:
                varVal = U(binding.name)
                var = Variable(varVal)
                term = castToTerm(binding.xml_select('*')[0])
                currBind[var]=term
            if currBind:
                actualRT.append(currBind)
    return actualRT
        
class TestSequence(unittest.TestCase):
    verbose = False
    def setUp(self):
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.network.nsMap = nsMap
        self.rules=list(HornFromN3(open('SPARQL/W3C/rdf-rdfs.n3')))

def test_generator(testName, label, queryFile, rdfDoc, regime, result, debug):
    def test(self,debug=debug):
        print testName, label
        query = urlopen(queryFile).read()
        factGraph = Graph().parse(urlopen(rdfDoc),format='n3')
        factGraph.parse(open('SPARQL/W3C/rdfs-axiomatic-triples.n3'),format='n3')
        self.rules.extend(self.network.setupDescriptionLogicProgramming(
                                                     factGraph,
                                                     addPDSemantics=True,
                                                     constructNetwork=False))
        if debug:
            pprint(list(self.rules))
        topDownStore=TopDownSPARQLEntailingStore(
                        factGraph.store,
                        factGraph,
                        idb=self.rules,
                        DEBUG=debug,
                        nsBindings=nsMap,
                        decisionProcedure = BFP_METHOD,
                        identifyHybridPredicates = True,
                        templateMap={
                            STRING.contains : "REGEX(%s,%s)"
                        })
        targetGraph = Graph(topDownStore)
        parsedQuery=parse(query)
        for pref,nsUri in (setdict(nsMap) | setdict(
                parsedQuery.prolog.prefixBindings)).items():
            targetGraph.bind(pref,nsUri)
        # rt=targetGraph.query('',parsedQuery=parsedQuery)
        actualSolns=[ImmutableDict([(k,v)
                        for k,v in d.items()])
                            for d in parseResults(
                                targetGraph.query(query).serialize(
                                                        format='xml'))]
        expectedSolns=[ImmutableDict([(k,v)
                        for k,v in d.items()])
                            for d in parseResults(urlopen(result).read())]
        actualSolns.sort(key=lambda d:hash(d))
        expectedSolns.sort(key=lambda d:hash(d))
        self.failUnless(set(actualSolns) == set(expectedSolns),
                        "Answers don't match %s v.s. %s"%(actualSolns,
                                                          expectedSolns)
        )
        if debug:
            for network,goal in topDownStore.queryNetworks:
                pprint(goal)
                network.reportConflictSet(True)
    return test

if __name__ == '__main__':
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--profile',
                  action='store_true',
                  default=False,
      help = 'Whether or not to run a profile')
    op.add_option('--singleTest',
      help = 'The short name of the test to run')
    op.add_option('--debug','-v',
                  action='store_true',
                  default=False,
      help = 'Run the test in verbose mode')
    (options, facts) = op.parse_args()

    for test, name, queryFile, rdfDoc, regime, result in GetTests():
        if test in SKIP or options.singleTest is not None and options.singleTest != test:
            if test in SKIP:
                print "\tSkipping (%s)"%test,SKIP[test]#>>sys.stderr,SKIP[test],
        elif regime in SUPPORTED_ENTAILMENT:
            test_name = 'test_%s' % test
            test = test_generator(test, name, queryFile, rdfDoc, regime, result, options.debug)
            setattr(TestSequence, test_name, test)
    if options.profile:
        from hotshot import Profile, stats
        p = Profile('fuxi.profile')
        p.runcall(unittest.TextTestRunner(verbosity=5).run,
                  unittest.makeSuite(TestSequence))
        p.close()
        s = stats.load('fuxi.profile')
        s.strip_dirs()
        s.sort_stats('time','cumulative','pcalls')
        s.print_stats(.1)
        s.print_callers(.05)
        s.print_callees(.05)
    else:
        unittest.TextTestRunner(verbosity=5).run(
            unittest.makeSuite(TestSequence)
        )
