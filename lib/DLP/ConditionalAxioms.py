# -*- coding: utf-8 -*-
import rdflib

rdflib.plugin.register(
    'sparql', rdflib.query.Processor,
    'rdflib.plugins.sparql.processor', 'SPARQLProcessor')

rdflib.plugin.register(
    'sparql', rdflib.query.Result,
    'rdflib.plugins.sparql.processor', 'SPARQLResult')

LIST_MEMBERSHIP_SEMANTICS = \
    """
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix list: <http://www.w3.org/2000/10/swap/list#>.

{?L rdf:first ?I} => {?I list:in ?L}.
{?L rdf:rest ?R. ?I list:in ?R} => {?I list:in ?L}.
"""

NOMINAL_SEMANTICS = \
    """
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
@prefix list: <http://www.w3.org/2000/10/swap/list#>.

#For OWL/oneOf
{?C owl:oneOf ?L. ?X list:in ?L} => {?X a ?C}.
"""

FUNCTIONAL_SEMANTICS = \
    """
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix log: <http://www.w3.org/2000/10/swap/log#>.

#Inverse functional semantics
{?P a owl:FunctionalProperty. ?S ?P ?O. ?S ?P ?Y. ?O log:notEqualTo ?Y } => {?O = ?Y}.
{?P a owl:InverseFunctionalProperty. ?S ?P ?O. ?Y ?P ?O. ?S log:notEqualTo ?Y } => {?S = ?Y}.

#owl:sameAs is symmetric, transitive and supports "smushing."
{?T1 = ?T2} => {?T2 = ?T1}.
{?T1 = ?T2. ?S = ?T1} => {?S = ?T2}.
{?T1 ?P ?O. ?T1 = ?T2.} => {?T2 ?P ?O}.
"""

DIFFERENT_FROM_SEMANTICS = \
    """
@prefix owl: <http://www.w3.org/2002/07/owl#>.
@prefix log: <http://www.w3.org/2000/10/swap/log#>.
@prefix list: <http://www.w3.org/2000/10/swap/list#>.

{ ?ANY a owl:AllDifferent; owl:distinctMembers ?L. ?L1 list:in ?L. ?L2 list:in ?L. ?L1 log:notEqualTo ?L2 } => { ?L1 owl:differentFrom ?L2 }.
"""

FUNCTIONAL_PROPERTIES = \
    """
ASK {
  [] a ?KIND
  FILTER(
      ?KIND = owl:InverseFunctionalProperty ||
      ?KIND = owl:FunctionalProperty
  )
}"""


def AdditionalRules(tBox):
    """
    Only include list and oneOf semantics if oneOf axiom is detected in graph

    reduce computational complexity.  Same with other conditional axioms

    """
    from FuXi.Horn.HornRules import HornFromN3
    try:
        from functools import reduce
        assert reduce
    except ImportError:
        pass
    try:
        from io import StringIO
        assert StringIO
    except ImportError:
        from StringIO import StringIO

    from rdflib import RDF
    from FuXi.Syntax.InfixOWL import OWL_NS

    ruleSrc = set()
    addListSemantics = False

    if tBox.query(FUNCTIONAL_PROPERTIES, initNs={"owl": OWL_NS}).askAnswer:
        ruleSrc.add(FUNCTIONAL_SEMANTICS)

    if (None, OWL_NS.oneOf, None) in tBox:
        ruleSrc.add(NOMINAL_SEMANTICS)
        addListSemantics = True

    if (None, RDF.type, OWL_NS.AllDifferent) in tBox:
        ruleSrc.add(DIFFERENT_FROM_SEMANTICS)
        addListSemantics = True

    if addListSemantics:
        ruleSrc.add(LIST_MEMBERSHIP_SEMANTICS)

    for src in ruleSrc:
        for rule in HornFromN3(StringIO(src)):
            yield rule

# from FuXi.DLP.ConditionalAxioms import DIFFERENT_FROM_SEMANTICS
# from FuXi.DLP.ConditionalAxioms import FUNCTIONAL_PROPERTIES
# from FuXi.DLP.ConditionalAxioms import FUNCTIONAL_SEMANTICS
# from FuXi.DLP.ConditionalAxioms import LIST_MEMBERSHIP_SEMANTICS
# from FuXi.DLP.ConditionalAxioms import NOMINAL_SEMANTICS

# from FuXi.DLP.ConditionalAxioms import AdditionalRules
