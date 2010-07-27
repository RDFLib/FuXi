from pprint import pprint, pformat
from sets import Set
from FuXi.Rete import *
from FuXi.Syntax.InfixOWL import *
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import LEFT_MEMORY,RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet
from FuXi.Horn.PositiveConditions import Uniterm, BuildUnitermFromTuple
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from FuXi.Horn.HornRules import HornFromN3
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Rete.Magic import *
from FuXi.Rete.SidewaysInformationPassing import *
from FuXi.Rete.TopDown import PrepareSipCollection, SipStrategy, RDFTuplesToSPARQL
from FuXi.Rete.Proof import ProofBuilder, PML, GMP_NS
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef
#from rdflib.OWL import FunctionalProperty -- invalid / unused import deleted
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
from glob import glob
from rdflib.sparql.parser import parse
import unittest, os, time, itertools

RDFLIB_CONNECTION=''
RDFLIB_STORE='IOMemory'

CWM_NS    = Namespace("http://cwmTest/")
DC_NS     = Namespace("http://purl.org/dc/elements/1.1/")
STRING_NS = Namespace("http://www.w3.org/2000/10/swap/string#")
MATH_NS   = Namespace("http://www.w3.org/2000/10/swap/math#")
FOAF_NS   = Namespace("http://xmlns.com/foaf/0.1/") 
OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")
TEST_NS   = Namespace("http://metacognition.info/FuXi/DL-SHIOF-test.n3#")
LOG       = Namespace("http://www.w3.org/2000/10/swap/log#")
RDF_TEST  = Namespace('http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#')
OWL_TEST  = Namespace('http://www.w3.org/2002/03owlt/testOntology#')
LIST      = Namespace('http://www.w3.org/2000/10/swap/list#')

queryNsMapping={'test':'http://metacognition.info/FuXi/test#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'foaf':'http://xmlns.com/foaf/0.1/',
                'dc':'http://purl.org/dc/elements/1.1/',
                'rss':'http://purl.org/rss/1.0/',
                'rdfs':'http://www.w3.org/2000/01/rdf-schema#',
                'rdf':'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
                'owl':OWL_NS,
                'rdfs':RDF.RDFNS,
}

nsMap = {
  u'rdfs' :RDFS.RDFSNS,
  u'rdf'  :RDF.RDFNS,
  u'rete' :RETE_NS,
  u'owl'  :OWL_NS,
  u''     :TEST_NS,
  u'otest':OWL_TEST,
  u'rtest':RDF_TEST,
  u'foaf' :URIRef("http://xmlns.com/foaf/0.1/"),
  u'math' :URIRef("http://www.w3.org/2000/10/swap/math#"),
}

MANIFEST_QUERY = \
"""
SELECT ?status ?premise ?conclusion ?feature ?descr
WHERE {
  [ 
    a otest:PositiveEntailmentTest;
    otest:feature ?feature;
    rtest:description ?descr;
    rtest:status ?status;
    rtest:premiseDocument ?premise;
    rtest:conclusionDocument ?conclusion 
  ]
}"""
PARSED_MANIFEST_QUERY = parse(MANIFEST_QUERY)

Features2Skip = [
    URIRef('http://www.w3.org/2002/07/owl#sameClassAs'),
]

TopDownTests2Skip = [
    'OWL/FunctionalProperty/Manifest002.rdf', #requires second order predicate derivation 
    'OWL/unionOf/Manifest002.rdf', # support for disjunctive horn logic 
    'OWL/FunctionalProperty/Manifest004.rdf',
    'OWL/oneOf/Manifest002.rdf', #requires second order predicate derivation
    'OWL/InverseFunctionalProperty/Manifest002.rdf', 
    'OWL/InverseFunctionalProperty/Manifest004.rdf',
    'OWL/oneOf/Manifest003.rdf', #Requires quantification over predicate symbol (2nd order)    
]

Tests2Skip = [
      
    'OWL/InverseFunctionalProperty/Manifest001.rdf',
    'OWL/FunctionalProperty/Manifest001.rdf', #owl:sameIndividualAs deprecated
    'OWL/Nothing/Manifest002.rdf',# owl:sameClassAs deprecated
]

patterns2Skip = [
    'OWL/cardinality',
    'OWL/samePropertyAs'
]

def tripleToTriplePattern(graph,triple):
    return "%s %s %s"%tuple([renderTerm(graph,term) 
                                for term in triple])

def renderTerm(graph,term):
    if term == RDF.type:
        return ' a '
    else:
        try:
            return isinstance(term,BNode) and term.n3() or graph.qname(term)
        except:
            return term.n3()

class OwlTestSuite(unittest.TestCase):
    def setUp(self):
        store = plugin.get(RDFLIB_STORE,Store)()
        store.open(RDFLIB_CONNECTION)
        self.ruleStore=N3RuleStore()
        self.ruleGraph = Graph(self.ruleStore)
        self.ruleFactsGraph = Graph(store)
        self.network = ReteNetwork(self.ruleStore,nsMap=nsBinds)
        
        #renderNetwork(self.network,nsMap=nsMap).write_graphviz('owl-rules.dot')
    def tearDown(self):
        pass
    
    def calculateEntailments(self, factGraph):
        start = time.time()  
        self.network.feedFactsToAdd(generateTokenSet(factGraph))                    
        sTime = time.time() - start
        if sTime > 1:
            sTimeStr = "%s seconds"%sTime
        else:
            sTime = sTime * 1000
            sTimeStr = "%s milli seconds"%sTime
        print "Time to calculate closure on working memory: ",sTimeStr
        print self.network
        
        tNodeOrder = [tNode 
                        for tNode in self.network.terminalNodes 
                            if self.network.instanciations.get(tNode,0)]
        tNodeOrder.sort(key=lambda x:self.network.instanciations[x],reverse=True)
        for termNode in tNodeOrder:
            print termNode
            print "\t", termNode.clause
            print "\t\t%s instanciations"%self.network.instanciations[termNode]
    #                    for c in AllClasses(factGraph):
    #                        print CastClass(c,factGraph)
        print "=============="
        self.network.inferredFacts.namespace_manager = factGraph.namespace_manager
        return sTimeStr

    def MagicOWLProof(self,goals,rules,factGraph,conclusionFile):
        progLen = len(rules)
        magicRuleNo = 0
        dPreds = []
        for rule in AdditionalRules(factGraph):
            print "\tAdding ", rule
            rules.append(rule)            

        if TOP_DOWN == 'open':
            goals = [(Variable('SUBJECT'),goalP,goalO) 
                        for goalS,goalP,goalO in goals 
                            if goalP != RDF.type or goalO.find(OWL_NS)==-1]
        
        for rule in MagicSetTransformation(factGraph,
                                           rules,
                                           goals,
                                           dPreds):
            magicRuleNo+=1
            self.network.buildNetworkFromClause(rule)    
            self.network.rules.add(rule)
        dPreds.append(LIST['in'])
        print "rate of reduction in the size of the program: ", (100-(float(magicRuleNo)/float(progLen))*100)
        if TOP_DOWN == 'ground':
            print "ASK { %s }"%('\n'.join([tripleToTriplePattern(factGraph,
                                                                goal) 
                                  for goal in goals ]))
            timings = 0
            pprint(list(factGraph.adornedProgram))            
            sipCollection = PrepareSipCollection(factGraph.adornedProgram)

            self.network.nsMap['pml'] = PML
            self.network.nsMap['gmp'] = GMP_NS
            for goal in goals:
                derivedAnswer = first(SipStrategy(
                                   goal,
                                   sipCollection,
                                   factGraph,
                                   dPreds,
                                   bindings={},
                                   network = self.network,
                                   debug = DEBUG))
                self.failUnless(derivedAnswer, "Failed to prove ground goal")
                if not derivedAnswer:
                    raise
                    print "failed top-down derivation"
                else:
                    ans,ns = derivedAnswer
                    self.failUnless(ans, "Failed to prove ground goal")
                    print "=== Passed! ==="
        elif TOP_DOWN == 'open':
            nsMap.update(dict([(k,v) 
                         for k,v in factGraph.namespaces()]))
            topDownStore=TopDownSPARQLEntailingStore(
                                        factGraph.store,
                                        factGraph,
                                        set(dPreds),
                                        rules,
                                        nsBindings=nsMap,
                                        DEBUG=DEBUG) 
            #targetGraph = ConjunctiveGraph(topDownStore)
            targetGraph = Graph(topDownStore)
            topDownStore.targetGraph = targetGraph 
            topDownStore.targetGraph.templateMap = {     LOG.equal:"%s = %s",
                                                    LOG.notEqualTo: "%s != %s" }
            topDownStore.edb.templateMap = topDownStore.targetGraph.templateMap
            for pref,nsUri in nsMap.items():
                targetGraph.bind(pref,nsUri)
            for goalS,goalP,goalO in goals:
                if goalP == RDF.type and goalO.find(OWL_NS)+1:
                        continue                
                sVar = Variable('SUBJECT')
                query=RDFTuplesToSPARQL(
                            [BuildUnitermFromTuple((sVar,goalP,goalO))],
                             factGraph,
                             vars=[sVar])
                print "Open goal to solve ", query
                rt=targetGraph.query(query,initNs=nsMap)
                self.failUnless((goalS) in rt, "Failed top-down re-write derivation")
                if (goalS) in rt:
                    print "=== Passed! ==="
                else:
                    raise
                    print "failed top-down re-write derivation"
        else:
            for goal in goals:
                goal=AdornLiteral(goal).makeMagicPred().toRDFTuple()
                factGraph.add(goal)
            timing=self.calculateEntailments(factGraph)
            for goal in goals:
                if goal not in self.network.inferredFacts and goal not in factGraph:
                    print "missing triple %s"%(pformat(goal))
                    from FuXi.Rete.Util import renderNetwork 
                    pprint([BuildUnitermFromTuple(t) for t in self.network.inferredFacts])
                    dot=renderNetwork(self.network,self.network.nsMap).write_jpeg('test-fail.jpeg')
                    self.network.reportConflictSet(True)
                    raise #Exception ("Failed test: "+feature)
                else:
                    print "=== Passed! ==="
            return timing
       
    def testOwl(self): 
        testData = {}       
        for manifest in glob('OWL/*/Manifest*.rdf'):
            if manifest in Tests2Skip:
                continue
            if TOP_DOWN and manifest in TopDownTests2Skip:
                continue
            skip = False
            for pattern2Skip in patterns2Skip:
                if manifest.find(pattern2Skip) > -1:
                    skip = True
                    break
            if skip:
                continue            
            manifestStore = plugin.get(RDFLIB_STORE,Store)()
            manifestGraph = Graph(manifestStore)
            manifestGraph.parse(open(manifest))
            rt = manifestGraph.query(
                                      MANIFEST_QUERY,
                                      initNs=nsMap,
                                      DEBUG = False)
            #print list(manifestGraph.namespace_manager.namespaces())
            for status,premise,conclusion, feature, description in rt:
                if feature in Features2Skip:
                    continue
                premise = manifestGraph.namespace_manager.compute_qname(premise)[-1]
                conclusion = manifestGraph.namespace_manager.compute_qname(conclusion)[-1]
                premiseFile    = '/'.join(manifest.split('/')[:2]+[premise])
                conclusionFile = '/'.join(manifest.split('/')[:2]+[conclusion])
                print premiseFile
                print conclusionFile
                if status == 'APPROVED':
                    if SINGLE_TEST and premiseFile != SINGLE_TEST:
                        continue
                    assert os.path.exists('.'.join([premiseFile,'rdf'])) 
                    assert os.path.exists('.'.join([conclusionFile,'rdf']))
                    print "<%s> :- <%s>"%('.'.join([conclusionFile,'rdf']),
                                          '.'.join([premiseFile,'rdf']))
                    store = plugin.get(RDFLIB_STORE,Store)()
                    store.open(RDFLIB_CONNECTION)
                    factGraph = Graph(store)
                    factGraph.parse(open('.'.join([premiseFile,'rdf'])))
                    allFacts = ReadOnlyGraphAggregate([factGraph,self.ruleFactsGraph])
                    Individual.factoryGraph=factGraph
                    
                    for c in AllClasses(factGraph):
                        if not isinstance(c.identifier,BNode):
                            print c.__repr__(True)       
                            
                    if MAGIC_PROOFS:
                        if feature in TopDownTests2Skip:
                            continue
                        print premiseFile,feature,description
                        program=list(HornFromN3(StringIO(non_DHL_OWL_Semantics)))
                        program.extend(self.network.setupDescriptionLogicProgramming(
                                                                     factGraph,
                                                                     addPDSemantics=False,
                                                                     constructNetwork=False))                        
                        print "Original program"
#                        pprint(program)
                        timings=[]  
                        #Magic set algorithm is initiated by a query, a single horn ground, 'fact'                    
                        try:   
                            goals=set()
                            for triple in Graph(store).parse('.'.join([conclusionFile,'rdf'])):
                                if triple not in factGraph:
                                    goals.add(triple)
                            timings.append(self.MagicOWLProof(goals,program,factGraph,conclusionFile))
                            self.network._resetinstanciationStats()
                            self.network.reset()
                            self.network.clear()                                
                        except:
#                            print "missing triple %s"%(pformat(goal))
                            print manifest, premiseFile
                            print "feature: ", feature
                            print description
                            from FuXi.Rete.Util import renderNetwork 
                            pprint([BuildUnitermFromTuple(t) for t in self.network.inferredFacts])
#                            dot=renderNetwork(self.network,self.network.nsMap).write_jpeg('test-fail.jpeg')
                            raise #Exception ("Failed test: "+feature)
                            
                        testData[manifest] = timings    
                        continue
                    else:
                        self.network.setupDescriptionLogicProgramming(factGraph,addPDSemantics=True)
                        sTimeStr=self.calculateEntailments(factGraph)
                        expectedFacts = Graph(store)                    
                        for triple in expectedFacts.parse('.'.join([conclusionFile,'rdf'])):
                            closureGraph = ReadOnlyGraphAggregate([self.network.inferredFacts,factGraph])
                            if triple not in self.network.inferredFacts and triple not in factGraph:
                                print "missing triple %s"%(pformat(triple))
                                print manifest
                                print "feature: ", feature
                                print description
                                pprint(list(self.network.inferredFacts))  
#                                pprint(programs)                          
                                raise Exception ("Failed test: "+feature)
                            else:
                                print "=== Passed! ==="
                                #pprint(list(self.network.inferredFacts))
                        print "\n"
                        testData[manifest] = sTimeStr
                        store.rollback()
                        self.network.reset()
                        self.network._resetinstanciationStats()
                    
#        pprint(testData)

def runTests(options):
    global MAGIC_PROOFS,TOP_DOWN, SINGLE_TEST, DEBUG 
    SINGLE_TEST  = options.singleTest   
    MAGIC_PROOFS = options.bottomUp
    DEBUG        = options.debug
    if options.bottomUp:
        TOP_DOWN = False
    TOP_DOWN = options.topDown
    suite = unittest.makeSuite(OwlTestSuite)
    if options.profile:
        #from profile import Profile
        from hotshot import Profile, stats
        p = Profile('fuxi.profile')
        #p = Profile()
        for i in range(options.runs):
            p.runcall(unittest.TextTestRunner(verbosity=5).run,suite)
        p.close()    
        s = stats.load('fuxi.profile')
#        s=p.create_stats()
        s.strip_dirs()
        s.sort_stats('time','cumulative','pcalls')
        s.print_stats(.1)
        s.print_callers(.05)
        s.print_callees(.05)
    else:
        unittest.TextTestRunner(verbosity=5).run(suite)
                
if __name__ == '__main__':
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
    op.add_option('--bottomUp', 
                  action='store_true',
                  default=True,
      help = 'Whether or not to solve the OWL test cases via magic set and bottom-up')    
    op.add_option('--profile', 
                  action='store_true',
                  default=False,
      help = 'Whether or not to run a profile')    
    op.add_option('--singleTest', 
                  default='',
      help = 'The identifier for the test to run')        
    op.add_option('--debug','-v', 
                  action='store_true',
                  default=False,
      help = 'Run the test in verbose mode')        
    
    op.add_option('--runs', 
                  type='int',
                  default=1,
      help = 'The number of times to run the test to accumulate data for profiling')            
    op.add_option('--topDown', 
                  default='ground',
                  choices = ['ground', 
                             'open'],                  
      help = 'Whether or not to solve the OWL test cases via magic set, top-down '+
      'and either ground queries (resulting in yes/no answers) or open queries '+
      ' (resulting in bindings which when subsstituted should result in the original query)')
    (options, facts) = op.parse_args()
    
    runTests(options)