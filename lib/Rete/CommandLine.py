#!/usr/bin/env python
from pprint import pprint
from FuXi.Rete.Proof import GenerateProof
from FuXi.Rete import ReteNetwork
from FuXi.Rete.AlphaNode import SUBJECT,PREDICATE,OBJECT,VARIABLE
from FuXi.Rete.BetaNode import PartialInstanciation, LEFT_MEMORY, RIGHT_MEMORY
from FuXi.Rete.RuleStore import N3RuleStore, SetupRuleStore
from FuXi.Rete.Util import renderNetwork,generateTokenSet, xcombine
from FuXi.DLP.DLNormalization import NormalFormReduction
from FuXi.DLP import MapDLPtoNetwork, non_DHL_OWL_Semantics
from FuXi.Horn import ComplementExpansion
from FuXi.Horn.HornRules import HornFromN3, Ruleset
from FuXi.Syntax.InfixOWL import *
from rdflib.Namespace import Namespace
from rdflib import plugin,RDF,RDFS,URIRef,URIRef,Literal,Variable
from rdflib.store import Store
from cStringIO import StringIO
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.syntax.NamespaceManager import NamespaceManager
import unittest, time, warnings,sys

def main():
    from optparse import OptionParser
    op = OptionParser('usage: %prog [options] factFile1 factFile2 ... factFileN')
    op.add_option('--closure', 
                  action='store_true',
                  default=False,
      help = 'Whether or not to serialize the inferred triples'+ 
             ' along with the original triples.  Otherwise '+
              '(the default behavior), serialize only the inferred triples')
    op.add_option('--output', 
                  default='n3',
                  metavar='RDF_FORMAT',
                  choices = ['xml', 
                             'TriX', 
                             'n3', 
                             'nt',
                             'rif',
                             'rif-xml',
                             'conflict',
                             'man-owl'],
      help = "Serialize the inferred triples and/or original RDF triples to STDOUT "+
             "using the specified RDF syntax ('xml','pretty-xml','nt','turtle', "+
             "or 'n3') or to print a summary of the conflict set (from the RETE "+
             "network) if the value of this option is 'conflict'.  If the the "+
             " value is 'rif' or 'rif-xml', Then the rules used for inference "+
             "will be serialized as RIF.  Finally if the value is 'man-owl', then "+
             "the RDF facts are assumed to be OWL/RDF and serialized via Manchester OWL "+
             "syntax.  The default is %default")
    op.add_option('--class',
                  dest='classes',
                  action='append',
                  default=[],
                  metavar='QNAME', 
      help = 'Used with --output=man-owl to determine which '+
             'classes within the entire OWL/RDF are targetted for serialization'+
             '.  Can be used more than once')
    op.add_option('--property',
                  action='append',
                  dest='properties',
                  default=[],
                  metavar='QNAME', 
      help = 'Used with --output=man-owl or --extract to determine which '+
             'properties are serialized / extracted.  Can be used more than once')
    op.add_option('--normalize', 
                  action='store_true',
                  default=False,
      help = "Used with --output=man-owl to attempt to determine if the ontology is 'normalized' [Rector, A. 2003]"+
      "The default is %default")
    op.add_option('--input-format', 
                  default='xml',
                  dest='inputFormat',
                  metavar='RDF_FORMAT',
                  choices = ['xml', 'trix', 'n3', 'nt', 'rdfa'],
      help = "The format of the RDF document(s) which serve as the initial facts "+
             " for the RETE network. One of 'xml','n3','trix', 'nt', "+
             "or 'rdfa'.  The default is %default")
    op.add_option('--pDSemantics', 
                  action='store_true',
                  default=False,
      help = 'Used with --dlp to add pD semantics ruleset for semantics not covered '+
      'by DLP but can be expressed in definite Datalog Logic Programming'+
      ' The default is %default')
    op.add_option('--stdin', 
                  action='store_true',
                  default=False,
      help = 'Parse STDIN as an RDF graph to contribute to the initial facts. The default is %default ')
    op.add_option('--ns', 
                  action='append',
                  default=[],
                  metavar="PREFIX=URI",
      help = 'Register a namespace binding (QName prefix to a base URI).  This '+
             'can be used more than once')
    op.add_option('--rules', 
                  default=[],
                  action='append',
                  metavar='PATH_OR_URI',
      help = 'The Notation 3 documents to use as rulesets for the RETE network'+
      '.  Can be specified more than once')
    op.add_option('--filter', 
                  action='append',
                  default=[],
                  metavar='PATH_OR_URI',
      help = 'The Notation 3 documents to use as a filter (entailments do not particpate in network)')
    op.add_option('--ruleFacts', 
                  action='store_true',
                  default=False,
      help = "Determines whether or not to attempt to parse initial facts from "+
      "the rule graph.  The default is %default")
    op.add_option('--dlp', 
                  action='store_true',
                  default=False,
      help = 'Use Description Logic Programming (DLP) to extract rules from OWL/RDF.  The default is %default')
    op.add_option('--negation', 
                  action='store_true',
                  default=False,                
      help = 'Extract negative rules?')    
    op.add_option('--normalForm', 
                  action='store_true',
                  default=False,                
      help = 'Whether or not to reduce DL axioms & LP rules to a normal form')        
    (options, facts) = op.parse_args()
    
    nsBinds = {'iw':'http://inferenceweb.stanford.edu/2004/07/iw.owl#'}
    for nsBind in options.ns:
        pref,nsUri = nsBind.split('=')
        nsBinds[pref]=nsUri
    
    namespace_manager = NamespaceManager(Graph())
    factGraph = Graph() 
    ruleSet = Ruleset()

    for fileN in options.rules:
        if options.ruleFacts:
            factGraph.parse(fileN,format='n3')
            print >>sys.stderr,"Parsing RDF facts from ", fileN
        rs = HornFromN3(fileN)
        nsBinds.update(rs.nsMapping)
        ruleSet.formulae.extend(rs)
        #ruleGraph.parse(fileN,format='n3')

    ruleSet.nsMapping = nsBinds

    for prefix,uri in nsBinds.items():
        namespace_manager.bind(prefix, uri, override=False)
    closureDeltaGraph = Graph()
    closureDeltaGraph.namespace_manager = namespace_manager
    factGraph.namespace_manager = namespace_manager

    for fileN in facts:
        factGraph.parse(fileN,format=options.inputFormat)
        
    if options.stdin:
        factGraph.parse(sys.stdin,format=options.inputFormat)
        
    if options.normalForm:
        NormalFormReduction(factGraph)
                
    workingMemory = generateTokenSet(factGraph)

    rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
    network.inferredFacts = closureDeltaGraph
    network.nsMap = nsBinds
    
    if options.dlp:
        dlp=network.setupDescriptionLogicProgramming(
                                 factGraph,
                                 addPDSemantics=options.pDSemantics,
                                 constructNetwork=False,
                                 ignoreNegativeStratus=options.negation)        
        ruleSet.formulae.extend(dlp)
    if options.output == 'rif':
        for rule in ruleSet:
            print rule
        if options.negation:
            for nRule in network.negRules:
                print nRule
        
    elif options.output == 'man-owl':
        cGraph = network.closureGraph(factGraph,readOnly=False)
        cGraph.namespace_manager = namespace_manager
        Individual.factoryGraph = cGraph
        if options.classes:
            mapping = dict(namespace_manager.namespaces())
            for c in options.classes:
                pref,uri=c.split(':')
                print Class(URIRef(mapping[pref]+uri)).__repr__(True)
        elif options.properties:
            mapping = dict(namespace_manager.namespaces())
            for p in options.properties:
                pref,uri=p.split(':')
                print Property(URIRef(mapping[pref]+uri))
        else:
            for p in AllProperties(cGraph):
                print p.identifier
                print repr(p)
            for c in AllClasses(cGraph):
                if options.normalize:
                    if c.isPrimitive():
                        primAnc = [sc for sc in c.subClassOf if sc.isPrimitive()] 
                        if len(primAnc)>1:
                            warnings.warn("Branches of primitive skeleton taxonomy"+
                              " should form trees: %s has %s primitive parents: %s"%(
                             c.qname,len(primAnc),primAnc),UserWarning,1)
                        children = [desc for desc in c.subSumpteeIds()]
                        for child in children:
                            for otherChild in [o for o in children if o is not child]:
                                if not otherChild in [c.identifier 
                                          for c in Class(child).disjointWith]:# and\
                                    warnings.warn("Primitive children (of %s) "+
                                          "must be mutually disjoint: %s and %s"%(
                                      c.qname,
                                      Class(child).qname,
                                      Class(otherChild).qname),UserWarning,1)
                if not isinstance(c.identifier,BNode):
                    print c.__repr__(True)
    for rule in ruleSet:
        network.buildNetworkFromClause(rule)

    for fileN in options.filter:
        for rule in HornFromN3(fileN):
            network.buildFilterNetworkFromClause(rule)

    start = time.time()  
    network.feedFactsToAdd(workingMemory)
    sTime = time.time() - start
    if sTime > 1:
        sTimeStr = "%s seconds"%sTime
    else:
        sTime = sTime * 1000
        sTimeStr = "%s milli seconds"%sTime
    print >>sys.stderr,"Time to calculate closure on working memory: ",sTimeStr
    print >>sys.stderr, network
    if options.filter:
        print >>sys.stderr,"Applying filter to entailed facts"
        network.inferredFacts = network.filteredFacts

    if options.output == 'conflict':
        network.reportConflictSet()
    elif options.output not in ['rif','rif-xml','man-owl']:
        if options.closure:
            cGraph = network.closureGraph(factGraph)
            cGraph.namespace_manager = namespace_manager
            print cGraph.serialize(destination=None, 
                                   format=options.output, 
                                   base=None)
        else:
            print network.inferredFacts.serialize(destination=None, 
                                                  format=options.output, 
                                                  base=None)