from pprint import pprint, pformat
from sets import Set
from FuXi.Rete import *
from FuXi.Syntax.InfixOWL import *
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import LEFT_MEMORY,RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet
from FuXi.Horn.PositiveConditions import Uniterm, BuildUnitermFromTuple
from FuXi.Horn.HornRules import HornFromN3
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Rete.Magic import MagicSetTransformation, iterCondition, AdornLiteral
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef
from rdflib.OWL import FunctionalProperty
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
from glob import glob
from rdflib.sparql.bison import Parse
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

MAGIC_PROOFS = True

SINGLE_TEST=''#OWL/FunctionalProperty/premises003'

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
PARSED_MANIFEST_QUERY = Parse(MANIFEST_QUERY)

Features2Skip = [
    URIRef('http://www.w3.org/2002/07/owl#sameClassAs'),
]

Features2SkipMagic = [
    #FunctionalProperty
]

Tests2Skip = [
    'OWL/oneOf/Manifest003.rdf', #logical set equivalence?  
    'OWL/differentFrom/Manifest002.rdf'  ,#needs log:notEqualTo 
    'OWL/distinctMembers/Manifest001.rdf',#needs log:notEqualTo and list semantics of AllDifferent 
    'OWL/unionOf/Manifest002.rdf',#can't implement set theoretic union for owl:unionOf.
    'OWL/InverseFunctionalProperty/Manifest001.rdf',#owl:sameIndividualAs deprecated
    'OWL/FunctionalProperty/Manifest001.rdf', #owl:sameIndividualAs deprecated
    'OWL/Nothing/Manifest002.rdf',# owl:sameClassAs deprecated
    'OWL/AllDifferent/Manifest001.rdf',#requires support for built-ins (log:notEqualTo)
    #Fix for magic set implementation
    #'OWL/TransitiveProperty/Manifest001.rdf', #recursive logic program
    #'OWL/InverseFunctionalProperty/Manifest002.rdf', #need to investigate
]

patterns2Skip = [
    'OWL/cardinality',
    'OWL/samePropertyAs'
]

class OwlTestSuite(unittest.TestCase):
    def setUp(self):
        store = plugin.get(RDFLIB_STORE,Store)()
        store.open(RDFLIB_CONNECTION)
        self.ruleStore=N3RuleStore()
        self.ruleGraph = Graph(self.ruleStore)
        self.ruleFactsGraph = Graph(store)
#        if not MAGIC_PROOFS:
#            self.ruleGraph.parse(StringIO(non_DHL_OWL_Semantics),format='n3')
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
#        if self.network.inferredFacts:
#            print "Implicit facts: "
#            print self.network.inferredFacts.serialize(format='turtle')
#        print "ruleset after MST:"                    
#        pprint(list(self.network.rules))
#        print "rate of reduction in the size of the program: ", len len(self.network.rules)
        return sTimeStr

    def MagicOWLProof(self,goals,rules,factGraph,conclusionFile):
#        print "Goals",[AdornLiteral(goal) for goal in goals]
        assert not self.network.rules
        progLen = len(rules)
        magicRuleNo = 0
        for rule in MagicSetTransformation(factGraph,
                                           rules,
                                           goals):
            magicRuleNo+=1
            self.network.buildNetworkFromClause(rule)    
            self.network.rules.add(rule)
        print "rate of reduction in the size of the program: ", (100-(float(magicRuleNo)/float(progLen))*100)
        for goal in goals:
            goal=AdornLiteral(goal).makeMagicPred().toRDFTuple()
            factGraph.add(goal)
        timing=self.calculateEntailments(factGraph)
#        print self.network.closureGraph(factGraph,readOnly=True).serialize(format='n3')
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
                if goal in self.network.inferredFacts:
                    from FuXi.Rete.Proof import GenerateProof
                    builder,proof=GenerateProof(self.network,goal)
#                    pGraph=Graph()
#                    dot=builder.renderProof(goal,
#                                            self.network.nsMap).write_jpeg('proofs/%s.jpeg'%conclusionFile.replace('/','-'))                
        return timing
       
    def testOwl(self): 
        testData = {}       
        for manifest in glob('OWL/*/Manifest*.rdf'):
            if manifest in Tests2Skip:
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
                                      PARSED_MANIFEST_QUERY,
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
                    
#                    for c in AllClasses(factGraph):
#                        if not isinstance(c.identifier,BNode):
#                            print c.__repr__(True)       
                            
                    if MAGIC_PROOFS:
                        if feature in Features2SkipMagic:
                            continue
                        print premiseFile,feature,description
                        program=list(HornFromN3(StringIO(non_DHL_OWL_Semantics)))
                        program.extend(self.network.setupDescriptionLogicProgramming(
                                                                     factGraph,
                                                                     addPDSemantics=False,
                                                                     constructNetwork=False))
#                        print "Original program"
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
                            dot=renderNetwork(self.network,self.network.nsMap).write_jpeg('test-fail.jpeg')
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

def runTests(profile=False):
    suite = unittest.makeSuite(OwlTestSuite)
    if profile:
        #from profile import Profile
        from hotshot import Profile, stats
        p = Profile('fuxi.profile')
        #p = Profile()
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
    runTests(profile=False)