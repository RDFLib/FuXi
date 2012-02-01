#!/usr/bin/env python
# encoding: utf-8
"""
Helper Functions for reducing DL axioms into a normal forms
"""
from cStringIO import StringIO
try:
    from rdflib.graph import Graph
    from rdflib import Namespace, RDF, RDFS, URIRef, Variable, Literal, BNode
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph
    from rdflib import URIRef, RDF, RDFS, Namespace, Variable, Literal, URIRef, BNode
    from rdflib.syntax.NamespaceManager import NamespaceManager

from rdflib.util import first
from FuXi.Rete import ReteNetwork
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.Syntax.InfixOWL import *
from FuXi.DLP import SKOLEMIZED_CLASS_NS
#from FuXi.Rete.Magic import MagicSetTransformation
import sys, unittest

class NominalRangeTransformer(object):        
    NOMINAL_QUERY=\
    """SELECT ?RESTRICTION ?INTERMEDIATE_CLASS ?NOMINAL ?PROP
       { ?RESTRICTION owl:onProperty ?PROP;
                      owl:someValuesFrom ?INTERMEDIATE_CLASS .  
         ?INTERMEDIATE_CLASS owl:oneOf ?NOMINAL .  } """    
    
    def transform(self,graph):
        """
        Transforms a 'pure' nominal range into a disjunction of value restrictions
        """
        Individual.factoryGraph = graph
        for restriction,intermediateCl,nominal,prop in graph.query(
                                 self.NOMINAL_QUERY,
                                 initNs={u'owl':OWL_NS}):
            nominalCollection=Collection(graph,nominal)
            #purge restriction
            restr=Class(restriction)
            parentSets = [i for i in restr.subClassOf]
            restr.clearOutDegree()
            newConjunct=BooleanClass(restriction,
                                     OWL_NS.unionOf,
                                     [Property(prop)|value|val 
                                                 for val in nominalCollection],
                                     graph)
            newConjunct.subClassOf = parentSets
            
            #purge nominalization placeholder
            iClass = BooleanClass(intermediateCl)
            iClass.clear()
            iClass.delete()

class UniversalNominalRangeTransformer(object):        
    NOMINAL_QUERY=\
    """SELECT ?RESTRICTION ?INTERMEDIATE_CLASS ?NOMINAL ?PROP ?PARTITION
       { ?RESTRICTION owl:onProperty ?PROP;
                      owl:allValuesFrom ?INTERMEDIATE_CLASS .  
         ?INTERMEDIATE_CLASS owl:oneOf ?NOMINAL .
         ?PROP rdfs:range [ owl:oneOf ?PARTITION ] .
       } """    
    
    def transform(self,graph):
        """
        Transforms a universal restriction on a 'pure' nominal range into a 
        conjunction of value restriction (using set theory and demorgan's laws)
        """
        Individual.factoryGraph = graph
        for restriction,intermediateCl,nominal,prop, partition in graph.query(
                                 self.NOMINAL_QUERY,
                                 initNs={u'owl':OWL_NS,
                                         u'rdfs':RDFS}):
            exceptions = EnumeratedClass()
            partition = Collection(graph,partition)
            nominalCollection=Collection(graph,nominal)
            for i in partition:
                if i not in nominalCollection:
                    exceptions._rdfList.append(i)
                    #exceptions+=i 
            exists=Class(complementOf=(Property(prop)|some|exceptions))
            for s,p,o in graph.triples((None,None,restriction)):
                graph.add((s,p,exists.identifier))
            Individual(restriction).delete()

            #purge nominalization placeholder
            iClass = BooleanClass(intermediateCl)
            iClass.clear()
            iClass.delete()
            
class GeneralUniversalTransformer(object):
    def transform(self,graph):
        """
        Transforms a universal restriction to a negated existential restriction
        """
        Individual.factoryGraph = graph
        for restr,p,o in graph.triples((None,OWL_NS.allValuesFrom,None)):
            graph.remove((restr,p,o))
            innerCompl = Class(complementOf=o)
            graph.add((restr,OWL_NS.someValuesFrom,innerCompl.identifier))
            outerCompl = Class()
            for _s,_p,_o in graph.triples((None,None,restr)):
                graph.add((_s,_p,outerCompl.identifier))
                graph.remove((_s,_p,_o))
            outerCompl.complementOf=restr

class DoubleNegativeTransformer(object):
    UNIVERSAL_QUERY=\
    """SELECT ?COMPL1 ?COMPL2 ?COMPL3
       { ?COMPL1 owl:complementOf ?COMPL2 .
         ?COMPL2 owl:complementOf ?COMPL3
         FILTER( isBlank(?COMPL1) && isBlank(?COMPL2) )
       } """
    
    def transform(self,graph):
        Individual.factoryGraph = graph
        for compl1,compl2,compl3 in graph.query(
                                 self.UNIVERSAL_QUERY,
                                 initNs={u'owl':OWL_NS,
                                         u'rdfs':RDFS}):
            Individual(compl1).replace(compl3)
            Individual(compl2).delete()

            
class DemorganTransformer(object):        
    def transform(self,graph):
        """
        Uses demorgan's laws to reduce negated disjunctions to a conjunction of
        negated formulae
        """
        Individual.factoryGraph = graph
        for disjunctId in graph.subjects(predicate=OWL_NS.unionOf):
            if (None,OWL_NS.complementOf,disjunctId) in graph and \
               isinstance(disjunctId,BNode):
                #not (     A1 or      A2  or .. or      An ) 
                #                 = 
                #    ( not A1 and not A2 and .. and not An )
                disjunct = BooleanClass(disjunctId,operator=OWL_NS.unionOf)
                items = list(disjunct)
                newConjunct = BooleanClass(members=[~Class(item) for item in items])
                for negation in graph.subjects(predicate=OWL_NS.complementOf,
                                               object=disjunctId):
                    Class(negation).replace(newConjunct)
                    if not isinstance(negation,BNode):
                        newConjunct.identifier = negation        
                disjunct.clear()
                disjunct.delete()
            elif ((disjunctId,OWL_NS.unionOf,None) in graph) and not \
                   [item for item in BooleanClass(disjunctId,
                                                  operator=OWL_NS.unionOf)
                        if not Class(item).complementOf]:
                #( not A1 or  not A2  or .. or  not An ) 
                #                 = 
                #not ( A1 and A2 and .. and An )                         
                disjunct = BooleanClass(disjunctId,operator=OWL_NS.unionOf)
                items = [Class(item).complementOf for item in disjunct]
                for negation in disjunct:
                    Class(negation).delete()
                negatedConjunct = ~ BooleanClass(members=items)
                disjunct.clear()
                disjunct.replace(negatedConjunct)

class ConjunctionFlattener(object):        
    def transform(self,graph):
        """
        Flattens conjunctions
        ( A1 and ( B1 and B2 ) and A2 ) 
                         = 
        ( A1 and B1 and B2 and A2 )
        
        """
        Individual.factoryGraph = graph
        for conjunctId in graph.subjects(predicate=OWL_NS.intersectionOf):
            conjunct = BooleanClass(conjunctId)
            nestedConjuncts = [BooleanClass(i) for i in conjunct
                                    if (i,OWL_NS.intersectionOf,None) in graph]
            if nestedConjuncts:
                def collapseConjunctTerms(left,right):
                    list(left)+list(right)
                if len(nestedConjuncts) == 1:
                    newTopLevelItems = list(nestedConjuncts[0])
                else:
                    newTopLevelItems = reduce(collapseConjunctTerms,nestedConjuncts)
                for nc in nestedConjuncts:
                    nc.clear()
                    del conjunct[conjunct.index(nc.identifier)]
                    nc.delete()
                for newItem in newTopLevelItems:
                    conjunct.append(newItem)
            
def NormalFormReduction(ontGraph):
    UniversalNominalRangeTransformer().transform(ontGraph)
    GeneralUniversalTransformer().transform(ontGraph)
    DoubleNegativeTransformer().transform(ontGraph)    
    NominalRangeTransformer().transform(ontGraph)
    DemorganTransformer().transform(ontGraph)
    DoubleNegativeTransformer().transform(ontGraph)    
    ConjunctionFlattener().transform(ontGraph)

EX_NS = Namespace('http://example.com/')
EX    = ClassNamespaceFactory(EX_NS)

class ReductionTestA(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
        partition = EnumeratedClass(EX_NS.part,
                                    members=[EX_NS.individual1,
                                             EX_NS.individual2,
                                             EX_NS.individual3])
        subPartition = EnumeratedClass(EX_NS.partition,members=[EX_NS.individual1])
        partitionProp = Property(EX_NS.propFoo,
                                 range=partition)
        self.foo = EX.foo
        self.foo.subClassOf = [partitionProp|only|subPartition] 
        
    def testUnivInversion(self):
        UniversalNominalRangeTransformer().transform(self.ontGraph)
        self.failUnlessEqual(len(list(self.foo.subClassOf)),
                             1,
                             "There should still be one subsumed restriction")
        subC = CastClass(first(self.foo.subClassOf))
        self.failUnless(not isinstance(subC,Restriction),
                        "subclass of a restriction")
        self.failUnless(subC.complementOf is not None,"Should be a complement!")
        innerC = CastClass(subC.complementOf)
        self.failUnless(isinstance(innerC,Restriction),
                        "complement of a restriction, not %r"%innerC)
        self.failUnlessEqual(innerC.onProperty,
                             EX_NS.propFoo,
                             "restriction on propFoo")
        self.failUnless(innerC.someValuesFrom,"converted to an existential restriction not %r"%innerC)
        invertedC = CastClass(innerC.someValuesFrom)
        self.failUnless(isinstance(invertedC,EnumeratedClass),
                        "existencial restriction on enumerated class")
        self.assertEqual(len(invertedC),
                         2,
                        "existencial restriction on enumerated class of length 2")
        self.assertEqual(repr(invertedC),
                         "{ ex:individual2 ex:individual3 }",
                         "The negated partition should exclude individual1")
        NominalRangeTransformer().transform(self.ontGraph)
        DemorganTransformer().transform(self.ontGraph)
        
        subC = CastClass(first(self.foo.subClassOf))
        self.assertEqual(repr(subC),
                        "( ( not ( ex:propFoo value ex:individual2 ) ) and ( not ( ex:propFoo value ex:individual3 ) ) )")

class ReductionTestB(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
        disjunct = (~ EX.alpha) | (~ EX.omega)
        self.foo = EX.foo
        disjunct+=self.foo 
        
    def testHiddenDemorgan(self):
        NormalFormReduction(self.ontGraph)
        self.failUnless(first(self.foo.subClassOf).complementOf,
                        "should be the negation of a boolean class")
        innerC = CastClass(first(self.foo.subClassOf).complementOf)
        self.failUnless(isinstance(innerC,BooleanClass) and \
                        innerC._operator == OWL_NS.intersectionOf,
                        "should be the negation of a conjunct")        
        self.assertEqual(repr(innerC),"( ex:alpha and ex:omega )")

class FlatteningTest(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
        nestedConjunct = EX.omega & EX.gamma
        self.topLevelConjunct = EX.alpha & nestedConjunct
        
    def testFlatenning(self):
        self.assertEquals(repr(self.topLevelConjunct),
                          "ex:alpha that ( ex:omega and ex:gamma )")
        ConjunctionFlattener().transform(self.ontGraph)
        self.assertEquals(repr(self.topLevelConjunct),
                          "( ex:alpha and ex:omega and ex:gamma )")

class UniversalComplementXFormTest(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph

    def testUniversalInversion(self):
        testClass1 = EX.omega & (Property(EX_NS.someProp)|only|~EX.gamma)
        testClass1.identifier = EX_NS.Foo
        self.assertEquals(repr(testClass1),
                          "ex:omega that ( ex:someProp only ( not ex:gamma ) )")
        NormalFormReduction(self.ontGraph)
        self.assertEquals(repr(testClass1),
                          "ex:omega that ( not ( ex:someProp some ex:gamma ) )")
    
if __name__ == '__main__':
    unittest.main()
