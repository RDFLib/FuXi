#--
"""
===================================================================================
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
from pprint import pprint
# from FuXi.DLP import non_DHL_OWL_Semantics as SUBSUMPTION_SEMANTICS
from FuXi.DLP import SKOLEMIZED_CLASS_NS
from FuXi.DLP import SkolemizeExistentialClasses
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from FuXi.Syntax.InfixOWL import AllClasses
from FuXi.Syntax.InfixOWL import BooleanClass
from FuXi.Syntax.InfixOWL import CastClass
from FuXi.Syntax.InfixOWL import Class
from FuXi.Syntax.InfixOWL import ClassNamespaceFactory
from FuXi.Syntax.InfixOWL import Individual
from FuXi.Syntax.InfixOWL import OWL_NS
from FuXi.Syntax.InfixOWL import Property
from FuXi.Syntax.InfixOWL import Restriction
from FuXi.Syntax.InfixOWL import some
from rdflib import (
    BNode,
    Namespace,
    OWL,
    RDF,
    RDFS,
    URIRef,
    Variable,
    )
try:
    from functools import reduce
except ImportError:
    pass
try:
    from io import StringIO
except ImportError:
    from StringIO import StringIO

import logging
log = logging.getLogger(__name__)

LIST_NS = Namespace('http://www.w3.org/2000/10/swap/list#')
KOR_NS = Namespace('http://korrekt.org/')
EX_NS = Namespace('http://example.com/')
EX_CL = ClassNamespaceFactory(EX_NS)

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

CONDITIONAL_THING_RULE = \
"""
@prefix kor:    <http://korrekt.org/>.
@prefix owl:    <http://www.w3.org/2002/07/owl#>.
@prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf:    <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix list:   <http://www.w3.org/2000/10/swap/list#>.

#Rule 4 (needs to be added conditionally - only if owl:Thing appears in the ontology)
{ ?C rdfs:subClassOf ?C } => { ?C rdfs:subClassOf owl:Thing }."""

RULES = \
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

LEFT_SUBSUMPTION_OPERAND = 0
RIGHT_SUBSUMPTION_OPERAND = 1
BOTH_SUBSUMPTION_OPERAND = 2
NEITHER_SUBSUMPTION_OPERAND = 3

SUBSUMPTION_SEMANTICS = u"""
@prefix log: <http://www.w3.org/2000/10/swap/log#>.
@prefix str: <http://www.w3.org/2000/10/swap/string#>.
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix xsd: <http://www.w3.org/2001/XMLSchema#>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix e: <http://eulersharp.sourceforge.net/2003/03swap/log-rules#>.
@prefix : <http://eulersharp.sourceforge.net/2003/03swap/rdfs-rules#>.


### Resource Description Framework RDF(S)

rdf:Alt rdfs:subClassOf rdfs:Container.
rdf:Bag rdfs:subClassOf rdfs:Container.
rdfs:ContainerMembershipProperty rdfs:subClassOf rdf:Property.
rdfs:Datatype rdfs:subClassOf rdfs:Class.
rdf:Seq rdfs:subClassOf rdfs:Container.
rdf:XMLLiteral rdfs:subClassOf rdfs:Literal; a rdfs:Datatype.

rdfs:comment rdfs:domain rdfs:Resource; rdfs:range rdfs:Literal.
rdfs:domain rdfs:domain rdf:Property; rdfs:range rdfs:Class.
rdf:first rdfs:domain rdf:List; rdfs:range rdfs:Resource; a owl:FunctionalProperty.
rdfs:isDefinedBy rdfs:domain rdfs:Resource; rdfs:range rdfs:Resource; rdfs:subPropertyOf rdfs:seeAlso.
rdfs:label rdfs:domain rdfs:Resource; rdfs:range rdfs:Literal.
rdfs:member rdfs:domain rdfs:Container; rdfs:range rdfs:Resource.
rdf:object rdfs:domain rdf:Statement; rdfs:range rdfs:Resource.
rdf:predicate rdfs:domain rdf:Statement; rdfs:range rdf:Property.
rdfs:range rdfs:domain rdf:Property; rdfs:range rdfs:Class.
rdf:rest rdfs:domain rdf:List; rdfs:range rdf:List; a owl:FunctionalProperty.
rdfs:seeAlso rdfs:domain rdfs:Resource; rdfs:range rdfs:Resource.
rdfs:subClassOf rdfs:domain rdfs:Class; rdfs:range rdfs:Class.
rdfs:subPropertyOf rdfs:domain rdf:Property; rdfs:range rdf:Property.
rdf:subject rdfs:domain rdf:Statement; rdfs:range rdfs:Resource.
rdf:type rdfs:domain rdfs:Resource; rdfs:range rdfs:Class.
rdf:value rdfs:domain rdfs:Resource; rdfs:range rdfs:Resource.

rdf:nil a rdf:List.


### inference rules for RDF(S)

{?S ?P ?O} => {?P a rdf:Property}.

{?P @has rdfs:domain ?C. ?S ?P ?O} => {?S a ?C}.

{?P @has rdfs:range ?C. ?S ?P ?O} => {?O a ?C}.

{?S ?P ?O} => {?S a rdfs:Resource}.
{?S ?P ?O} => {?O a rdfs:Resource}.

{?Q rdfs:subPropertyOf ?R. ?P rdfs:subPropertyOf ?Q} => {?P rdfs:subPropertyOf ?R}.

{?P @has rdfs:subPropertyOf ?R. ?S ?P ?O} => {?S ?R ?O}.

{?C a rdfs:Class} => {?C rdfs:subClassOf rdfs:Resource}.

{?A rdfs:subClassOf ?B. ?S a ?A} => {?S a ?B}.

{?B rdfs:subClassOf ?C. ?A rdfs:subClassOf ?B} => {?A rdfs:subClassOf ?C}.

{?X a rdfs:ContainerMembershipProperty} => {?X rdfs:subPropertyOf rdfs:member}.

{?X a rdfs:Datatype} => {?X rdfs:subClassOf rdfs:Literal}.


### inconsistency detections @@

{?S a rdf:XMLLiteral; e:clashesWith rdf:XMLLiteral} => false.
"""


def WhichSubsumptionOperand(term, owlGraph):
    topDownStore = TopDownSPARQLEntailingStore(
                    owlGraph.store,
                    owlGraph,
                    idb=HornFromN3(StringIO(SUBSUMPTION_SEMANTICS)),
                    DEBUG=False,
                    derivedPredicates=[OWL_NS.sameAs],
                    hybridPredicates=[OWL_NS.sameAs])
    targetGraph = Graph(topDownStore)
    appearsLeft = targetGraph.query(
            "ASK { <%s> rdfs:subClassOf [] } ",
            initNs={u'rdfs': RDFS})
    appearsRight = targetGraph.query(
            "ASK { [] rdfs:subClassOf <%s> } ",
            initNs={u'rdfs': RDFS})
    if appearsLeft and appearsRight:
        return BOTH_SUBSUMPTION_OPERAND
    elif appearsLeft:
        return LEFT_SUBSUMPTION_OPERAND
    else:
        return RIGHT_SUBSUMPTION_OPERAND


def StructuralTransformation(owlGraph, newOwlGraph):
    """
    Entry point for the transformation of the given ontology

    >>> EX = Namespace('http://example.com/')
    >>> EX_CL = ClassNamespaceFactory(EX)
    >>> graph = Graph()
    >>> graph.bind('ex', EX, True)
    >>> Individual.factoryGraph = graph
    >>> kneeJoint = EX_CL.KneeJoint
    >>> joint = EX_CL.Joint
    >>> knee  = EX_CL.Knee
    >>> isPartOf = Property(EX.isPartOf)
    >>> structure = EX_CL.Structure
    >>> leg = EX_CL.Leg
    >>> hasLocation = Property(EX.hasLocation)

    >>> kneeJoint.equivalentClass = [joint & (isPartOf | some | knee)]
    >>> legStructure = EX_CL.LegStructure
    >>> legStructure.equivalentClass = [structure & (isPartOf | some | leg)]
    >>> structure += leg
    >>> locatedInLeg = hasLocation | some | leg
    >>> locatedInLeg += knee

    >>> newGraph, conceptMap = StructuralTransformation(graph, Graph())
    >>> revDict = dict([(v, k) for k, v in conceptMap.items()])
    >>> newGraph.bind('ex', EX, True)
    >>> Individual.factoryGraph = newGraph

    Generated concepts can be listed ...

    .. code-block:: python

        for c in AllClasses(newGraph):
            if c.identifier in revDict:
                print("## New concept for %s ##" % revDict[c.identifier])
            print(c.__repr__(True))
            print("################################")

    """
    FreshConcept = {}
    newOwlGraph.bind('skolem', SKOLEMIZED_CLASS_NS, True)

    for cls in AllClasses(owlGraph):
        ProcessConcept(cls, owlGraph, FreshConcept, newOwlGraph)
    return newOwlGraph, FreshConcept


def ProcessConcept(klass, owlGraph, FreshConcept, newOwlGraph):
    """
    This method implements the pre-processing portion of the completion-based procedure
    and recursively transforms the input ontology one concept at a time
    """
    iD = klass.identifier
    #maps the identifier to skolem:bnodeLabel if
    #the identifier is a BNode or to skolem:newBNodeLabel
    #if its a URI
    FreshConcept[iD] = SkolemizeExistentialClasses(
        BNode() if isinstance(iD, URIRef) else iD
    )
    #A fresh atomic concept (A_c)
    newCls = Class(FreshConcept[iD], graph=newOwlGraph)

    cls = CastClass(klass, owlGraph)

    #determine if the concept is the left, right (or both)
    #operand of a subsumption axiom in the ontology
    location = WhichSubsumptionOperand(iD, owlGraph)
    # log.debug(repr(cls))
    if isinstance(iD, URIRef):
        #An atomic concept?
        if location in [LEFT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
            log.debug("Original (atomic) concept appears in the left HS of a subsumption axiom")
            #If class is left operand of subsumption operator,
            #assert (in new OWL graph) that A_c subsumes the concept
            _cls = Class(cls.identifier, graph=newOwlGraph)
            newCls += _cls
            log.debug("%s subsumes %s" % (newCls, _cls))
        if location in [RIGHT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
            log.debug("Original (atomic) concept appears in the right HS of a subsumption axiom")
            #If class is right operand of subsumption operator,
            #assert that it subsumes A_c
            _cls = Class(cls.identifier, graph=newOwlGraph)
            _cls += newCls
            log.debug("%s subsumes %s" % (_cls, newCls))
    elif isinstance(cls, Restriction):
        if location != NEITHER_SUBSUMPTION_OPERAND:
            #appears in at least one subsumption operator

            #An existential role restriction
            log.debug("Original (role restriction) appears in a subsumption axiom")
            role = Property(cls.onProperty, graph=newOwlGraph)

            fillerCls = ProcessConcept(
                            Class(cls.restrictionRange),
                            owlGraph,
                            FreshConcept,
                            newOwlGraph)
            #leftCls is (role SOME fillerCls)
            leftCls = role | some | fillerCls
            log.debug("let leftCls be %s" % leftCls)
            if location in [LEFT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the left operand, we say A_c subsumes
                #leftCls
                newCls += leftCls
                log.debug("%s subsumes leftCls" % newCls)
            if location in [RIGHT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
                #if appears as right operand, we say left Cls subsumes A_c
                leftCls += newCls
                log.debug("leftCls subsumes %s" % newCls)
    else:
        assert isinstance(cls, BooleanClass), "Not ELH ontology: %r" % cls
        assert cls._operator == OWL_NS.intersectionOf, "Not ELH ontology"
        log.debug("Original conjunction (or boolean operator wlog ) appears in a subsumption axiom")
        #A boolean conjunction
        if location != NEITHER_SUBSUMPTION_OPERAND:
            members = [ProcessConcept(Class(c),
                                      owlGraph,
                                      FreshConcept,
                                      newOwlGraph) for c in cls]
            newBoolean = BooleanClass(BNode(), members=members, graph=newOwlGraph)
            #create a boolean conjunction of the fresh concepts corresponding
            #to processing each member of the existing conjunction
            if location in [LEFT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the left operand, we say the new conjunction
                #is subsumed by A_c
                newCls += newBoolean
                log.debug("%s subsumes %s" % (newCls, newBoolean))
            if location in [RIGHT_SUBSUMPTION_OPERAND, BOTH_SUBSUMPTION_OPERAND]:
                #if appears as the right operand, we say A_c is subsumed by
                #the new conjunction
                newBoolean += newCls
                log.debug("%s subsumes %s" % (newBoolean, newCls))
    return newCls


def createTestOntGraph():
    graph = Graph()
    graph.bind('ex', EX_NS, True)
    Individual.factoryGraph = graph
    kneeJoint = EX_CL.KneeJoint
    joint = EX_CL.Joint

    knee = EX_CL.Knee
    isPartOf = Property(EX_NS.isPartOf)
    graph.add((isPartOf.identifier, RDF.type, OWL_NS.TransitiveProperty))
    structure = EX_CL.Structure
    leg = EX_CL.Leg
    hasLocation = Property(EX_NS.hasLocation, subPropertyOf=[isPartOf])
    # graph.add((hasLocation.identifier,RDFS.subPropertyOf,isPartOf.identifier))

    kneeJoint.equivalentClass = [joint & (isPartOf | some | knee)]
    legStructure = EX_CL.LegStructure
    legStructure.equivalentClass = [structure & (isPartOf | some | leg)]
    structure += leg
    structure += joint
    locatedInLeg = hasLocation | some | leg
    locatedInLeg += knee

    # log.debug(graph.serialize(format='n3'))

    # newGraph = Graph()
    # newGraph.bind('ex',EX_NS,True)

    # newGraph,conceptMap = StructuralTransformation(graph,newGraph)
    # revDict = dict([(v,k) for k,v in conceptMap.items()])

    # Individual.factoryGraph = newGraph
    # for oldConceptId ,newConceptId in conceptMap.items():
    #     if isinstance(oldConceptId,BNode):
    #         oldConceptRepr = repr(Class(oldConceptId,graph=graph))
    #         if oldConceptRepr.strip() == 'Some Class':
    #             oldConceptRepr = manchesterSyntax(
    #                 oldConceptId,
    #                 graph)
    #         log.debug("%s -> %s" % (
    #             oldConceptRepr,
    #             newConceptId
    #         ))

    #     else:
    #         log.debug("%s -> %s"%(
    #             oldConceptId,
    #             newConceptId
    #         ))

    # for c in AllClasses(newGraph):
    #     if isinstance(c.identifier,BNode) and c.identifier in conceptMap.values():
    #         log.debug("## %s ##" % c.identifier)
    #     else:
    #         log.debug("##" * 10)
    #     log.debug(c.__repr__(True))
    #     log.debug("################################")
    return graph


def SetupMetaInterpreter(tBoxGraph, goal, useThingRule=True):
    from FuXi.LP.BackwardFixpointProcedure import BackwardFixpointProcedure
    from FuXi.Rete.Magic import SetupDDLAndAdornProgram
    from FuXi.Horn.PositiveConditions import BuildUnitermFromTuple
    from FuXi.Rete.TopDown import PrepareSipCollection
    from FuXi.DLP import LloydToporTransformation, makeRule
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
            rule = makeRule(clause, {})
            # log.debug(rule)
            # PrettyPrintRule(rule)
            reducedCompletionRules.add(rule)

    network = SetupRuleStore(makeNetwork=True)[-1]
    SetupDDLAndAdornProgram(
        tBoxGraph,
        reducedCompletionRules,
        [goal],
        derivedPreds=derivedPredicates,
        ignoreUnboundDPreds=True,
        hybridPreds2Replace=hybridPredicates)

    lit = BuildUnitermFromTuple(goal)
    op = GetOp(lit)
    lit.setOperator(URIRef(op + u'_derived'))
    goal = lit.toRDFTuple()

    sipCollection = PrepareSipCollection(reducedCompletionRules)
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
    plog.debug(reducedCompletionRules)
    rt = bfp.answers(debug=True)
    plog.debug(rt)
    log.debug(bfp.metaInterpNetwork)
    bfp.metaInterpNetwork.reportConflictSet(True, sys.stderr)
    for query in bfp.edbQueries:
        log.debug("Dispatched query against dataset: ", query.asSPARQL())
    plog.debug(list(bfp.goalSolutions))


def NormalizeSubsumption(owlGraph):
    operands = [(clsLHS, clsRHS)
        for clsLHS, p, clsRHS in owlGraph.triples((None,
                                                 OWL_NS.equivalentClass,
                                                 None))]
    for clsLHS, clsRHS in operands:
        if isinstance(clsLHS, URIRef) and isinstance(clsRHS, URIRef):
            owlGraph.add((clsLHS, RDFS.subClassOf, clsRHS))
            owlGraph.add((clsRHS, RDFS.subClassOf, clsLHS))
            owlGraph.remove((clsLHS, OWL_NS.equivalentClass, clsRHS))
        elif isinstance(clsLHS, URIRef) and isinstance(clsRHS, BNode):
            owlGraph.add((clsLHS, RDFS.subClassOf, clsRHS))
            owlGraph.remove((clsLHS, OWL_NS.equivalentClass, clsRHS))
        elif isinstance(clsLHS, BNode) and isinstance(clsRHS, URIRef):
            owlGraph.add((clsRHS, RDFS.subClassOf, clsLHS))
            owlGraph.remove((clsLHS, OWL_NS.equivalentClass, clsRHS))

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
        log.debug(c.__repr__(True))
    SetupMetaInterpreter(ontGraph, goal)
#    test()
#    import doctest
#    doctest.testmod()

# from FuXi.DLP.CompletionReasoning import LIST_NS
# from FuXi.DLP.CompletionReasoning import KOR_NS
# from FuXi.DLP.CompletionReasoning import EX_NS
# from FuXi.DLP.CompletionReasoning import EX_CL
# from FuXi.DLP.CompletionReasoning import derivedPredicates
# from FuXi.DLP.CompletionReasoning import hybridPredicates
# from FuXi.DLP.CompletionReasoning import CONDITIONAL_THING_RULE
# from FuXi.DLP.CompletionReasoning import RULES
# from FuXi.DLP.CompletionReasoning import LEFT_SUBSUMPTION_OPERAND
# from FuXi.DLP.CompletionReasoning import RIGHT_SUBSUMPTION_OPERAND
# from FuXi.DLP.CompletionReasoning import BOTH_SUBSUMPTION_OPERAND
# from FuXi.DLP.CompletionReasoning import NEITHER_SUBSUMPTION_OPERAND

# from FuXi.DLP.CompletionReasoning import createTestOntGraph
# from FuXi.DLP.CompletionReasoning import NormalizeSubsumption
# from FuXi.DLP.CompletionReasoning import ProcessConcept
# from FuXi.DLP.CompletionReasoning import SetupMetaInterpreter
# from FuXi.DLP.CompletionReasoning import StructuralTransformation
# from FuXi.DLP.CompletionReasoning import WhichSubsumptionOperand


