#-- 
"""
Solution:
Unadorned:

Query: rdfs:subClassOf_bf(KneeJoint,?Class)
Query fact: rdfs:subClassOf_derived_query_bf(KneeJoint)

7. Forall ?C3 ?C2 ?C1 ( 
    rdfs:subClassOf_derived_bf(?C1 ?C3) 
        :- And( rdfs:subClassOf_derived_bf(?C1 ?C2) 
                rdfs:subClassOf_derived_bf(?C2 ?C3) ) )
                
		{ subClassOf }             -> ?C1 subClassOf_C1_C2
		{ subClassOf, subClassOf } -> ?C2 subClassOf_C2_C3




"""
__author__ = 'chimezieogbuji'
import sys
from FuXi.Syntax.InfixOWL              import *
from FuXi.DLP                          import SkolemizeExistentialClasses, SKOLEMIZED_CLASS_NS
from FuXi.Horn.HornRules               import HornFromN3
from FuXi.Rete.RuleStore               import SetupRuleStore
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from rdflib                            import RDF, RDFS, OWL, URIRef, Variable, BNode, Namespace
try:
    from rdflib.graph                  import Graph
except ImportError:
    from rdflib.Graph                  import Graph
    RDF = str(RDF.RDFNS)
    RDFS = str(RDFS.RDFSNS)
from rdflib import RDF, RDFS, Namespace, Variable, Literal, URIRef, BNode
from rdflib.util import first
from cStringIO                         import StringIO
from FuXi.Horn.HornRules               import HornFromN3

LIST_NS = Namespace('http://www.w3.org/2000/10/swap/list#')
KOR_NS  = Namespace('http://korrekt.org/')
EX_NS   = Namespace('http://example.com/')
EX_CL   = ClassNamespaceFactory(EX_NS)

derivedPredicates = [
    LIST_NS['in'],
    KOR_NS.subPropertyOf,
    RDFS.subClassOf,
    OWL.onProperty,
    OWL.someValuesFrom
]

hybridPredicates = [
    RDFS.subClassOf,
    OWL.onProperty,
    OWL.someValuesFrom
]

CONDITIONAL_THING_RULE=\
"""
@prefix kor:    <http://korrekt.org/>.
@prefix owl:    <http://www.w3.org/2002/07/owl#>.
@prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf:    <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix list:   <http://www.w3.org/2000/10/swap/list#>.

#Rule 4 (needs to be added conditionally - only if owl:Thing appears in the ontology)
{ ?C rdfs:subClassOf ?C } => { ?C rdfs:subClassOf owl:Thing }."""

RULES=\
"""
@prefix kor:    <http://korrekt.org/>.
@prefix owl:    <http://www.w3.org/2002/07/owl#>.
@prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf:    <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix list:   <http://www.w3.org/2000/10/swap/list#>.
#ELH completion rules in N3 / RIF / Datalog

{?L rdf:first ?I}               => {?I list:in ?L} .
{?L rdf:rest ?R. ?I list:in ?R} => {?I list:in ?L} .

#CTO: Sufficient to assert ?R kor:subPropertyOf ?R for all properties ?R in ontology?
{ ?P1 rdfs:subPropertyOf ?P2 } => { ?P1 kor:subPropertyOf ?P2 } .

#kor:subPropertyOf a owl:TransitiveProperty .
{ ?P1 kor:subPropertyOf ?P2 . ?P2 kor:subPropertyOf ?P3 } => { ?P1 kor:subPropertyOf ?P3 } .

#Rule 1
#rdfs:subClassOf a owl:TransitiveProperty
{ ?C1 rdfs:subClassOf ?C2 . ?C2 rdfs:subClassOf ?C3 } => { ?C1 rdfs:subClassOf ?C3 } .

#Rule 2 (CTO: Different from LL's formulation?)
{ ?C  rdfs:subClassOf ?CLASS .
  ?CLASS owl:intersectionOf ?L  .
  ?D list:in ?L  } => { ?C rdfs:subClassOf ?D } .
  
#Rule 3
{ ?C rdfs:subClassOf ?RESTRICTION .
  ?RESTRICTION owl:onProperty ?R ;
               owl:someValuesFrom ?D } => { ?D rdfs:subClassOf ?D } .

#Rule 5
{ ?C rdfs:subClassOf ?D1, ?D2 .
  ?D1 list:in ?L .
  ?D2 list:in ?L .
  ?E owl:intersectionOf ?L } => { ?C rdfs:subClassOf ?E } .

#Rule 6
{ ?C rdfs:subClassOf ?D .
  ?E owl:onProperty ?S ;
     owl:someValuesFrom ?D 
 } => { [ a owl:Restriction;
          owl:onProperty ?S ;
          owl:someValuesFrom ?C ] rdfs:subClassOf ?E } .

#Rule 7
{ ?D rdfs:subClassOf ?RESTRICTION1 .
  ?RESTRICTION1 owl:onProperty ?R ;
               owl:someValuesFrom ?C  .
  ?RESTRICTION2 owl:onProperty ?S ;
                owl:someValuesFrom ?C .
  ?RESTRICTION2 rdfs:subClassOf ?E .
  ?R kor:subPropertyOf ?S } => { ?D rdfs:subClassOf ?E } .

#Rule 8
{ ?D rdfs:subClassOf ?RESTRICTION1 .
  ?RESTRICTION1 owl:onProperty ?R ;
               owl:someValuesFrom ?C  .
  ?RESTRICTION2 owl:onProperty ?S ;
                owl:someValuesFrom ?C .
  ?RESTRICTION2 rdfs:subClassOf ?E .
  ?R kor:subPropertyOf ?T .
  ?T kor:subPropertyOf ?S .
  ?T a owl:TransitiveProperty } => {
  [ a owl:Restriction;
    owl:onProperty ?T ;
    owl:someValuesFrom ?D ] rdfs:subClassOf ?E } .
"""

LEFT_SUBSUMPTION_OPERAND    = 0
RIGHT_SUBSUMPTION_OPERAND   = 1
BOTH_SUBSUMPTION_OPERAND    = 2
NEITHER_SUBSUMPTION_OPERAND = 3

def WhichSubsumptionOperand(term,owlGraph):
    topDownStore=TopDownSPARQLEntailingStore(
                    owlGraph.store,
                    owlGraph,
                    idb=HornFromN3(StringIO(SUBSUMPTION_SEMANTICS)),
                    DEBUG=False,
                    derivedPredicates = [OWL_NS.sameAs],
                    hybridPredicates = [OWL_NS.sameAs])
    targetGraph = Graph(topDownStore)
    appearsLeft  = targetGraph.query(
            "ASK { <%s> rdfs:subClassOf [] } ",
            initNs={u'rdfs':RDFS})
    appearsRight = targetGraph.query(
            "ASK { [] rdfs:subClassOf <%s> } ",
            initNs={u'rdfs':RDFS})
    if appearsLeft and appearsRight:
        return BOTH_SUBSUMPTION_OPERAND
    elif appearsLeft:
        return LEFT_SUBSUMPTION_OPERAND
    else:
        return RIGHT_SUBSUMPTION_OPERAND

def StructuralTransformation(owlGraph,newOwlGraph):
    """
    Entry point for the transformation of the given ontology

    >>> EX = Namespace('http://example.com/')
    >>> EX_CL = ClassNamespaceFactory(EX)
    >>> graph = Graph()
    >>> graph.bind('ex',EX,True)
    >>> Individual.factoryGraph = graph
    >>> kneeJoint = EX_CL.KneeJoint
    >>> joint = EX_CL.Joint
    >>> knee  = EX_CL.Knee
    >>> isPartOf = Property(EX.isPartOf)
    >>> structure = EX_CL.Structure
    >>> leg = EX_CL.Leg
    >>> hasLocation = Property(EX.hasLocation)

    >>> kneeJoint.equivalentClass = [joint & (isPartOf|some|knee)]
    >>> legStructure = EX_CL.LegStructure
    >>> legStructure.equivalentClass = [structure & (isPartOf|some|leg)]
    >>> structure += leg
    >>> locatedInLeg = hasLocation|some|leg
    >>> locatedInLeg += knee

    >>> newGraph,conceptMap = StructuralTransformation(graph, Graph())
    >>> revDict = dict([(v,k) for k,v in conceptMap.items()])
    >>> newGraph.bind('ex',EX,True)
    >>> Individual.factoryGraph = newGraph
    >>> for c in AllClasses(newGraph):
    ...     if c.identifier in revDict: print "## New concept for %s ##"%revDict[c.identifier]
    ...     print c.__repr__(True)
    ...     print "################################"
    
    """
    FreshConcept = {}
    newOwlGraph.bind('skolem',SKOLEMIZED_CLASS_NS,True)

    for cls in AllClasses(owlGraph):
        ProcessConcept(cls,owlGraph,FreshConcept,newOwlGraph)
    return newOwlGraph, FreshConcept

def ProcessConcept(klass,owlGraph,FreshConcept,newOwlGraph):
    """
    This method implements the pre-processing portion of the completion-based procedure
    and recursively transforms the input ontology one concept at a time
    """
    iD = klass.identifier
    #maps the identifier to skolem:bnodeLabel if
    #the identifier is a BNode or to skolem:newBNodeLabel
    #if its a URI
    FreshConcept[iD] = SkolemizeExistentialClasses(
        BNode() if isinstance(iD,URIRef) else iD
    )
    #A fresh atomic concept (A_c)
    newCls = Class(FreshConcept[iD],graph=newOwlGraph)

    cls = CastClass(klass,owlGraph)

    #determine if the concept is the left, right (or both)
    #operand of a subsumption axiom in the ontology
    location = WhichSubsumptionOperand(iD,owlGraph)
    print repr(cls)
    if isinstance(iD,URIRef):
        #An atomic concept?
        if location in [LEFT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
            print "Original (atomic) concept appears in the left HS of a subsumption axiom"
            #If class is left operand of subsumption operator,
            #assert (in new OWL graph) that A_c subsumes the concept
            _cls   = Class(cls.identifier,graph=newOwlGraph)
            newCls += _cls
            print "%s subsumes %s"%(newCls,_cls)
        if location in [RIGHT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
            print "Original (atomic) concept appears in the right HS of a subsumption axiom"
            #If class is right operand of subsumption operator,
            #assert that it subsumes A_c
            _cls = Class(cls.identifier,graph=newOwlGraph)
            _cls += newCls
            print "%s subsumes %s"%(_cls,newCls)
    elif isinstance(cls,Restriction):
        if location != NEITHER_SUBSUMPTION_OPERAND:
            #appears in at least one subsumption operator

            #An existential role restriction
            print "Original (role restriction) appears in a subsumption axiom"
            role      = Property(cls.onProperty,graph=newOwlGraph)
                        
            fillerCls = ProcessConcept(
                            Class(cls.restrictionRange),
                            owlGraph,
                            FreshConcept,
                            newOwlGraph)
            #leftCls is (role SOME fillerCls)
            leftCls  = role|some|fillerCls
            print "let leftCls be %s"%leftCls
            if location in [LEFT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the left operand, we say A_c subsumes
                #leftCls
                newCls   += leftCls
                print "%s subsumes leftCls"%newCls
            if location in [RIGHT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
                #if appears as right operand, we say left Cls subsumes A_c
                leftCls  += newCls
                print "leftCls subsumes %s"%newCls
    else:
        assert isinstance(cls,BooleanClass),"Not ELH ontology: %r"%cls
        assert cls._operator == OWL_NS.intersectionOf,"Not ELH ontology"
        print "Original conjunction (or boolean operator wlog ) appears in a subsumption axiom"
        #A boolean conjunction
        if location != NEITHER_SUBSUMPTION_OPERAND:
            members = [ProcessConcept(Class(c),
                                      owlGraph,
                                      FreshConcept,
                                      newOwlGraph) for c in cls]
            newBoolean = BooleanClass(BNode(),members=members,graph=newOwlGraph)
            #create a boolean conjunction of the fresh concepts corresponding
            #to processing each member of the existing conjunction
            if location in [LEFT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the left operand, we say the new conjunction
                #is subsumed by A_c
                newCls     += newBoolean
                print "%s subsumes %s"%(newCls,newBoolean)
            if location in [RIGHT_SUBSUMPTION_OPERAND,BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the right operand, we say A_c is subsumed by
                #the new conjunction
                newBoolean += newCls
                print "%s subsumes %s"%(newBoolean,newCls)
    return newCls

def createTestOntGraph():
    graph = Graph()
    graph.bind('ex',EX_NS,True)
    Individual.factoryGraph = graph
    kneeJoint = EX_CL.KneeJoint
    joint = EX_CL.Joint
    
    knee  = EX_CL.Knee
    isPartOf = Property(EX_NS.isPartOf)
    graph.add((isPartOf.identifier,RDF.type,OWL_NS.TransitiveProperty))
    structure = EX_CL.Structure
    leg = EX_CL.Leg
    hasLocation = Property(EX_NS.hasLocation,subPropertyOf=[isPartOf])
    # graph.add((hasLocation.identifier,RDFS.subPropertyOf,isPartOf.identifier))

    kneeJoint.equivalentClass = [joint & (isPartOf|some|knee)]
    legStructure = EX_CL.LegStructure
    legStructure.equivalentClass = [structure & (isPartOf|some|leg)]
    structure += leg
    structure += joint
    locatedInLeg = hasLocation|some|leg
    locatedInLeg += knee
    

    # print graph.serialize(format='n3')

    # newGraph = Graph()
    # newGraph.bind('ex',EX_NS,True)

#    newGraph,conceptMap = StructuralTransformation(graph,newGraph)
#    revDict = dict([(v,k) for k,v in conceptMap.items()])

#    Individual.factoryGraph = newGraph
#    for oldConceptId ,newConceptId in conceptMap.items():
#        if isinstance(oldConceptId,BNode):
#            oldConceptRepr = repr(Class(oldConceptId,graph=graph))
#            if oldConceptRepr.strip() == 'Some Class':
#                oldConceptRepr = manchesterSyntax(
#                    oldConceptId,
#                    graph)
#            print "%s -> %s"%(
#                oldConceptRepr,
#                newConceptId
#            )
#
#        else:
#            print "%s -> %s"%(
#                oldConceptId,
#                newConceptId
#            )
#
#    for c in AllClasses(newGraph):
#        if isinstance(c.identifier,BNode) and c.identifier in conceptMap.values():
#            print "## %s ##"%c.identifier
#        else:
#            print "##" * 10
#        print c.__repr__(True)
#        print "################################"
    return graph

def SetupMetaInterpreter(tBoxGraph,goal,useThingRule=True):
    from FuXi.LP.BackwardFixpointProcedure    import BackwardFixpointProcedure
    from FuXi.Rete.Magic                      import SetupDDLAndAdornProgram, PrettyPrintRule
    from FuXi.Horn.PositiveConditions         import BuildUnitermFromTuple, Exists
    from FuXi.Rete.TopDown                    import PrepareSipCollection
    from FuXi.DLP                             import LloydToporTransformation, makeRule
    from FuXi.Rete.SidewaysInformationPassing import GetOp

    owlThingAppears = False
    if useThingRule and OWL.Thing in tBoxGraph.all_nodes():
        owlThingAppears = True
    completionRules = HornFromN3(StringIO(RULES))
    if owlThingAppears:
        completionRules.formulae.extend(
            HornFromN3(StringIO(CONDITIONAL_THING_RULE)))
    reducedCompletionRules = set()
    for rule in completionRules:
        for clause in LloydToporTransformation(rule.formula):
            rule = makeRule(clause,{})
            # print rule
#            PrettyPrintRule(rule)
            reducedCompletionRules.add(rule)

    network = SetupRuleStore(makeNetwork=True)[-1]
    SetupDDLAndAdornProgram(
        tBoxGraph,
        reducedCompletionRules,
        [goal],
        derivedPreds=derivedPredicates,
        ignoreUnboundDPreds = True,
        hybridPreds2Replace=hybridPredicates)

    lit = BuildUnitermFromTuple(goal)
    op = GetOp(lit)
    lit.setOperator(URIRef(op+u'_derived'))
    goal = lit.toRDFTuple()

    sipCollection=PrepareSipCollection(reducedCompletionRules)
    tBoxGraph.templateMap = {}
    bfp = BackwardFixpointProcedure(
                tBoxGraph,
                network,
                derivedPredicates,
                goal,
                sipCollection,
                hybridPredicates=hybridPredicates,
                debug=True)
    bfp.createTopDownReteNetwork(True)
    pprint(reducedCompletionRules)
    rt=bfp.answers(debug=True)
    pprint(rt)
    print >>sys.stderr, bfp.metaInterpNetwork
    bfp.metaInterpNetwork.reportConflictSet(True,sys.stderr)
    for query in bfp.edbQueries:
        print >>sys.stderr, "Dispatched query against dataset: ", query.asSPARQL()    
    pprint(list(bfp.goalSolutions))

def NormalizeSubsumption(owlGraph):
    operands = [(clsLHS,clsRHS) 
        for clsLHS,p,clsRHS in owlGraph.triples((None,
                                                 OWL_NS.equivalentClass,
                                                 None))]
    for clsLHS,clsRHS in operands:
        if isinstance(clsLHS,URIRef) and isinstance(clsRHS,URIRef):
            owlGraph.add((clsLHS,RDFS.subClassOf,clsRHS))
            owlGraph.add((clsRHS,RDFS.subClassOf,clsLHS))
            owlGraph.remove((clsLHS,OWL_NS.equivalentClass,clsRHS))
        elif isinstance(clsLHS,URIRef) and isinstance(clsRHS,BNode):
            owlGraph.add((clsLHS,RDFS.subClassOf,clsRHS))
            owlGraph.remove((clsLHS,OWL_NS.equivalentClass,clsRHS))
        elif isinstance(clsLHS,BNode) and isinstance(clsRHS,URIRef):
            owlGraph.add((clsRHS,RDFS.subClassOf,clsLHS))
            owlGraph.remove((clsLHS,OWL_NS.equivalentClass,clsRHS))
    
if __name__ == '__main__':
    goal = (EX_NS.KneeJoint,
            RDFS.subClassOf,
            Variable('Class'))
    ontGraph = createTestOntGraph()
    # ontGraph.add((EX_NS.KneeJoint,
    #               RDFS.subClassOf,
    #               EX_NS.KneeJoint))
    NormalizeSubsumption(ontGraph)
    for c in AllClasses(ontGraph):
        print c.__repr__(True)    
    SetupMetaInterpreter(ontGraph,goal)    
#    test()
#    import doctest
#    doctest.testmod()
