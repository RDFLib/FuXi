import sys, unittest, copy
try:
    from rdflib.graph import Graph
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph
    from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import RDF, RDFS, Namespace, Variable, Literal, URIRef, BNode
from rdflib.util import first
from FuXi.Rete.RuleStore import N3RuleStore,SetupRuleStore
from FuXi.Rete import ReteNetwork
from FuXi.Horn.PositiveConditions import PredicateExtentFactory
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.Syntax.InfixOWL import *
from FuXi.DLP import SKOLEMIZED_CLASS_NS, MapDLPtoNetwork, MalformedDLPFormulaError

EX_NS = Namespace('http://example.com/')
EX    = ClassNamespaceFactory(EX_NS)

class AdditionalDescriptionLogicTests(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph

    def testGCIConDisjunction(self):
        conjunct = EX.Foo & (EX.Omega | EX.Alpha)
        (EX.Bar) += conjunct
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              derivedPreds=[EX_NS.Bar],
                              addPDSemantics=False,
                              constructNetwork=False)
        self.assertEqual(repr(rules),
                         "[Forall ?X ( ex:Bar(?X) :- And( ex:Foo(?X) ex:Alpha(?X) ) ), Forall ?X ( ex:Bar(?X) :- And( ex:Foo(?X) ex:Omega(?X) ) )]")
        self.assertEqual(len(rules),
                         2,
                        "There should be 2 rules")

#    def testMalformedUnivRestriction(self):
#        someProp = Property(EX_NS.someProp)
#        conjunct = EX.Foo & (someProp|only|EX.Omega)
#        conjunct.identifier = EX_NS.Bar
#        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
#        self.failUnlessRaises(MalformedDLPFormulaError, 
#                              network.setupDescriptionLogicProgramming,
#                              self.ontGraph,
#                              derivedPreds=[EX_NS.Bar],
#                              addPDSemantics=False,
#                              constructNetwork=False)

    def testBasePredicateEquivalence(self):
        (EX.Foo).equivalentClass = [EX.Bar]
        self.assertEqual(repr(Class(EX_NS.Foo)),"Class: ex:Foo EquivalentTo: ex:Bar")
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              addPDSemantics=False,
                              constructNetwork=False)
        self.assertEqual(repr(rules),
                         "[Forall ?X ( ex:Bar(?X) :- ex:Foo(?X) ), Forall ?X ( ex:Foo(?X) :- ex:Bar(?X) )]")
        self.assertEqual(len(rules),
                         2,
                        "There should be 2 rules")

    def testExistentialInRightOfGCI(self):
        someProp = Property(EX_NS.someProp)
        existential = someProp|some|EX.Omega
        existential += EX.Foo
        self.assertEqual(repr(Class(EX_NS.Foo)),"Class: ex:Foo SubClassOf: ( ex:someProp SOME ex:Omega )")
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              addPDSemantics=False,
                              constructNetwork=False)
#        self.assertEqual(len(rules),
#                         1,
#                        "There should be 1 rule: %s"%rules)
#        rule=rules[0]
#        self.assertEqual(repr(rule.formula.body),
#                         "ex:Foo(?X)")             
#        self.assertEqual(len(rule.formula.head.formula),
#                         2)
        
    def testValueRestrictionInLeftOfGCI(self):
        someProp = Property(EX_NS.someProp)
        leftGCI = (someProp|value|EX.fish) & EX.Bar
        foo = EX.Foo
        foo+=leftGCI
        self.assertEqual(repr(leftGCI),
                         "ex:Bar THAT ( ex:someProp VALUE ex:fish )")
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              addPDSemantics=False,
                              constructNetwork=False)
        self.assertEqual(repr(rules),
                         "[Forall ?X ( ex:Foo(?X) :- And( ex:someProp(?X ex:fish) ex:Bar(?X) ) )]")
        
    def testNestedConjunct(self):
        nestedConj = (EX.Foo & EX.Bar) & EX.Baz
        (EX.Omega)+= nestedConj
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              addPDSemantics=False,
                              constructNetwork=False)
        for rule in rules:
            if rule.formula.head.arg[-1]==EX_NS.Omega:
                self.assertEqual(len(rule.formula.body),
                                 2)
                skolemPredicate = [term.arg[-1]
                         for term in rule.formula.body
                                if term.arg[-1].find(SKOLEMIZED_CLASS_NS)!=-1]
                self.assertEqual(len(skolemPredicate),
                                 1,
                                "Couldn't find skolem unary predicate!")
            else:
                self.assertEqual(len(rule.formula.body),
                                 2)
                skolemPredicate = rule.formula.head.arg[-1]
                self.failUnless(skolemPredicate.find(SKOLEMIZED_CLASS_NS)!=-1,
                                "Head should be a unary skolem predicate")
                skolemPredicate=skolemPredicate[0]
                
    def testOtherForm(self):
        contains   = Property(EX_NS.contains)
        locatedIn  = Property(EX_NS.locatedIn)
        topConjunct = (EX.Cath & 
                         (contains|some|
                            (EX.MajorStenosis & (locatedIn|value|EX_NS.LAD)))  &
                         (contains|some|
                            (EX.MajorStenosis & (locatedIn|value|EX_NS.RCA))))
        (EX.NumDisV2D)+=topConjunct
        from FuXi.DLP.DLNormalization import NormalFormReduction
        NormalFormReduction(self.ontGraph)
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        rules=network.setupDescriptionLogicProgramming(
                              self.ontGraph,
                              derivedPreds=[EX_NS.NumDisV2D],
                              addPDSemantics=False,
                              constructNetwork=False)
        from FuXi.Rete.Magic import PrettyPrintRule
        for rule in rules:
            PrettyPrintRule(rule)
            
    def testOtherForm2(self):
        hasCoronaryBypassConduit   = Property(EX_NS.hasCoronaryBypassConduit)

        ITALeft = EX.ITALeft
        ITALeft += (hasCoronaryBypassConduit|some|
                    EnumeratedClass(
                       members=[EX_NS.CoronaryBypassConduit_internal_thoracic_artery_left_insitu,
                                EX_NS.CoronaryBypassConduit_internal_thoracic_artery_left_free])) 
        from FuXi.DLP.DLNormalization import NormalFormReduction
        self.assertEquals(repr(Class(first(ITALeft.subSumpteeIds()))),"Some Class SubClassOf: Class: ex:ITALeft ")
        NormalFormReduction(self.ontGraph)
        self.assertEquals(repr(Class(first(ITALeft.subSumpteeIds()))),
                          "Some Class SubClassOf: Class: ex:ITALeft  . EquivalentTo: ( ( ex:hasCoronaryBypassConduit VALUE ex:CoronaryBypassConduit_internal_thoracic_artery_left_insitu ) OR ( ex:hasCoronaryBypassConduit VALUE ex:CoronaryBypassConduit_internal_thoracic_artery_left_free ) )")
                     
if __name__ == '__main__':
    unittest.main()
