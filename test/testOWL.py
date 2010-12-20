from pprint import pprint, pformat
from sets import Set
from FuXi.Rete import *
from FuXi.Syntax.InfixOWL import *
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import LEFT_MEMORY,RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore, SetupRuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet
from FuXi.Horn.PositiveConditions import Uniterm, BuildUnitermFromTuple
from FuXi.LP.BackwardFixpointProcedure import BackwardFixpointProcedure
from FuXi.LP import IdentifyHybridPredicates
from FuXi.SPARQL.BackwardChainingStore import * 
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from FuXi.Horn.HornRules import HornFromN3
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Rete.Magic import *
from FuXi.Rete.SidewaysInformationPassing import *
from FuXi.Rete.TopDown import PrepareSipCollection, SipStrategy
from FuXi.SPARQL import RDFTuplesToSPARQL, EDBQuery
from FuXi.Rete.Proof import ProofBuilder, PML, GMP_NS
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef
from rdflib.OWL import FunctionalProperty
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

NonNaiveSkip = [
    'OWL/oneOf/Manifest002.rdf', #see Issue 25
    'OWL/unionOf/Manifest002.rdf',                   # support for disjunctive horn logic 
]

MagicTest2Skip = [
    'OWL/oneOf/Manifest002.rdf',        #requires second order predicate derivation
    'OWL/oneOf/Manifest003.rdf',        #requires second order predicate derivation
    'OWL/disjointWith/Manifest001.rdf'  #requires second order predicate derivation
]


BFPTests2SKip = [
    'OWL/FunctionalProperty/Manifest002.rdf'       , #Haven't reconciled *all* 2nd order predicate queries
    'OWL/InverseFunctionalProperty/Manifest002.rdf', #  "         "        "    "
    # 'OWL/oneOf/Manifest002.rdf',                     #  "         "        "    "
    'OWL/oneOf/Manifest003.rdf',                     #  "         "        "    "
]

TopDownTests2Skip = [
    'OWL/FunctionalProperty/Manifest002.rdf', #requires second order predicate derivation 
    'OWL/FunctionalProperty/Manifest004.rdf',
    'OWL/InverseFunctionalProperty/Manifest002.rdf', 
    'OWL/InverseFunctionalProperty/Manifest004.rdf',
    'OWL/oneOf/Manifest003.rdf', #Requires quantification over predicate symbol (2nd order)    
    'OWL/AllDifferent/Manifest001.rdf' #Not sure why
]

Tests2Skip = [
      
    'OWL/InverseFunctionalProperty/Manifest001.rdf', #owl:sameIndividualAs deprecated
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
        rule_store, rule_graph, self.network = SetupRuleStore(makeNetwork=True)
        self.network.nsMap = nsBinds
        
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
            rules.append(rule)            
        if not GROUND_QUERY and REASONING_STRATEGY != 'gms':
            goalDict = dict([((Variable('SUBJECT'),goalP,goalO),goalS) 
                        for goalS,goalP,goalO in goals])
            goals = goalDict.keys()
        assert goals

        if REASONING_STRATEGY == 'gms':
            for rule in MagicSetTransformation(factGraph,
                                               rules,
                                               goals,
                                               dPreds):
                magicRuleNo+=1
                self.network.buildNetworkFromClause(rule)    
                self.network.rules.add(rule)
                if DEBUG:
                    print "\t", rule
            print "rate of reduction in the size of the program: ", (100-(float(magicRuleNo)/float(progLen))*100)
        
        if REASONING_STRATEGY in ['bfp','sld']:# and not GROUND_QUERY:
            reasoningAlg = TOP_DOWN_METHOD if REASONING_STRATEGY == 'sld' \
                           else BFP_METHOD
            topDownStore=TopDownSPARQLEntailingStore(
                            factGraph.store,
                            factGraph,
                            idb=rules,
                            DEBUG=DEBUG,
                            nsBindings=nsMap,
                            decisionProcedure = reasoningAlg,
                            identifyHybridPredicates = REASONING_STRATEGY == 'bfp')
            targetGraph = Graph(topDownStore)
            for pref,nsUri in nsMap.items():
                targetGraph.bind(pref,nsUri)
            start = time.time()                      
                        
            for goal in goals:
                queryLiteral = EDBQuery([BuildUnitermFromTuple(goal)],
                                        factGraph,
                                        None if GROUND_QUERY else [goal[0]])
                query = queryLiteral.asSPARQL()
                print "Goal to solve ", query
                rt=targetGraph.query(query,initNs=nsMap)
                if GROUND_QUERY:
                    self.failUnless(rt.askAnswer[0],"Failed top-down problem")
                else:                   
                    if (goalDict[goal]) not in rt or DEBUG:
                        for network,_goal in topDownStore.queryNetworks:
                            print network,_goal
                            network.reportConflictSet(True)
                        for query in topDownStore.edbQueries:
                            print query.asSPARQL()
                    self.failUnless((goalDict[goal]) in rt, 
                                    "Failed top-down problem")
            sTime = time.time() - start
            if sTime > 1:
                sTimeStr = "%s seconds"%sTime
            else:
                sTime = sTime * 1000
                sTimeStr = "%s milli seconds"%sTime
            return sTimeStr
        elif REASONING_STRATEGY == 'gms':
            for goal in goals:
                adornedGoalSeed = AdornLiteral(goal).makeMagicPred()
                goal=adornedGoalSeed.toRDFTuple()
                if DEBUG:
                    print "Magic seed fact ", adornedGoalSeed
                factGraph.add(goal)
            timing=self.calculateEntailments(factGraph)
            for goal in goals:
                # self.failUnless(goal in self.network.inferredFacts or goal in factGraph,
                #                 "Failed GMS query")
                if goal not in self.network.inferredFacts and goal not in factGraph:
                    print "missing triple %s"%(pformat(goal))
                    from FuXi.Rete.Util import renderNetwork 
                    pprint(list(factGraph.adornedProgram))
                    # dot=renderNetwork(self.network,self.network.nsMap).write_jpeg('test-fail.jpeg')
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
            if (REASONING_STRATEGY is not None and manifest in NonNaiveSkip) or\
               (REASONING_STRATEGY == 'sld' and manifest in TopDownTests2Skip) or \
               (REASONING_STRATEGY == 'bfp' and manifest in BFPTests2SKip) or\
               (REASONING_STRATEGY == 'gms' and manifest in MagicTest2Skip):
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
                    nsMap.update(dict([(k,v)
                                 for k,v in factGraph.namespaces()]))                    
                    if DEBUG:
                        print "## Source Graph ##\n", factGraph.serialize(format='n3')
                    Individual.factoryGraph=factGraph
                    
                    for c in AllClasses(factGraph):
                        if not isinstance(c.identifier,BNode):
                            print c.__repr__(True)       
                            
                    if feature in TopDownTests2Skip:
                        continue
                    print premiseFile,feature,description
                    program=list(HornFromN3(StringIO(non_DHL_OWL_Semantics)))
                    program.extend(self.network.setupDescriptionLogicProgramming(
                                                                 factGraph,
                                                                 addPDSemantics=False,
                                                                 constructNetwork=False))                        
                    print "Original program"
                    pprint(program)
                    timings=[]  

                    if REASONING_STRATEGY is None:
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
                                raise Exception ("Failed test: "+feature)
                            else:
                                print "=== Passed! ==="
                                #pprint(list(self.network.inferredFacts))
                        print "\n"
                        testData[manifest] = sTimeStr
                        store.rollback()
                        
                        self.setUp()                        
                        # self.network.reset()
                        # self.network._resetinstanciationStats()
                    else:
                        try:   
                            goals=[]
                            for triple in Graph(store).parse('.'.join([conclusionFile,'rdf'])):
                                if triple not in factGraph:
                                    goals.append(triple)
                            testData[manifest] = self.MagicOWLProof(goals,
                                                              program,
                                                              factGraph,
                                                              conclusionFile)
                                                              
                            self.setUp()
                            # self.network._resetinstanciationStats()
                            # self.network.reset()
                            # self.network.clear()                                
                        except:
    #                            print "missing triple %s"%(pformat(goal))
                            print manifest, premiseFile
                            print "feature: ", feature
                            print description
                            from FuXi.Rete.Util import renderNetwork 
                            pprint([BuildUnitermFromTuple(t) for t in self.network.inferredFacts])
    #                            dot=renderNetwork(self.network,self.network.nsMap).write_jpeg('test-fail.jpeg')
                            raise #Exception ("Failed test: "+feature)
                        
        pprint(testData)

def runTests(options):
    global REASONING_STRATEGY, GROUND_QUERY, SINGLE_TEST, DEBUG 
    SINGLE_TEST        = options.singleTest   
    DEBUG              = options.debug
    GROUND_QUERY       = options.groundQuery
    REASONING_STRATEGY = options.strategy

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
        for i in range(options.runs):        
            unittest.TextTestRunner(verbosity=5).run(suite)
            
def defaultOptions():
    class Holder(object):
        '''Empty class to add attributes to.'''
    options = Holder()
    options.__setattr__("groundQuery", False)
    options.__setattr__("profile", False)
    options.__setattr__("singleTest", '')
    options.__setattr__("debug", False)
    options.__setattr__("runs", 1)
    options.__setattr__("strategy", "gms")
    return options   

if __name__ == '__main__':
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options]')
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
    op.add_option('--groundQuery', 
                action='store_true',
                default=False,                  
      help = 'For top-down strategies, whether to solve ground triple patterns or not')
      
    op.add_option('--strategy', 
                  default='gms',
                  choices = ['gms','sld','bfp'],
      help = 'Which reasoning strategy to use in solving the OWL test cases '+
      'Use RETE-UL over re-written rules (gms), resolution-based top-down unification (sld),'+
      'or use RETE-UL as a backward fixpoint procedure (bfp) to simulate a top-down strategy via metainterpreter')
    (options, facts) = op.parse_args()
    
    runTests(options)