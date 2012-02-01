# -*- coding: utf-8 -*-
"""
Stratified Negation Semantics for DLP using SPARQL to handle the negation
"""
from pprint import pprint
try:
    from rdflib.graph import Graph
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph
    from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import Namespace, RDF, RDFS, Variable, Literal, URIRef, BNode
from rdflib.util import first
from FuXi.Rete.RuleStore import N3RuleStore,SetupRuleStore
from FuXi.Horn.PositiveConditions import And
from FuXi.Rete import ReteNetwork
from FuXi.Rete.RuleStore import N3RuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.Syntax.InfixOWL import *
from FuXi.DLP import SKOLEMIZED_CLASS_NS, MapDLPtoNetwork
from DLNormalization import NormalFormReduction
import sys, unittest, copy, itertools

EX_NS = Namespace('http://example.com/')
EX    = ClassNamespaceFactory(EX_NS)

def GetVars(atom):
    from FuXi.Rete.SidewaysInformationPassing import GetArgs
    return [term for term in GetArgs(atom) if isinstance(term,Variable)]

def CalculateStratifiedModel(network,ontGraph,derivedPreds,edb=None):
    posRules,ignored=MapDLPtoNetwork(network,
                               ontGraph,
                               constructNetwork=False,
                               derivedPreds=derivedPreds,
                               ignoreNegativeStratus=True)
    for rule in posRules:
        network.buildNetworkFromClause(rule)    
    network.feedFactsToAdd(generateTokenSet(edb and edb or ontGraph))
    for i in ignored:
        #Evaluate the Graph pattern, and instanciate the head of the rule with 
        #the solutions returned
        sel,compiler=StratifiedSPARQL(i)
        query=compiler.compile(sel)
        i.stratifiedQuery=query
        vars = sel.projection
        for rt in (edb and edb or ontGraph).query(query):
            solutions={}
            if isinstance(rt,tuple):
                solutions.update(dict([(vars[idx],i) for idx,i in enumerate(rt)]))
            else:
                solutions[vars[0]]=rt
            i.solutions=solutions
            head=copy.deepcopy(i.formula.head)
            head.ground(solutions)
            fact=head.toRDFTuple()
            network.inferredFacts.add(fact)
            network.feedFactsToAdd(generateTokenSet([fact]))
            
    #Now we need to clear assertions that cross the individual, concept, relation divide
    # toRemove=[]
    for s,p,o in network.inferredFacts.triples((None,
                                                RDF.type,
                                                None)):
        if s in (edb and edb or ontGraph).predicates() or\
           s in [_s for _s,_p,_o in 
                    (edb and edb or ontGraph).triples_choices(
                                        (None,
                                         RDF.type,
                                         [OWL_NS.Class,
                                          OWL_NS.Restriction]))]:
            network.inferredFacts.remove((s,p,o))
    return posRules,ignored
            
def createCopyPattern(toDo):
    """
    "Let φ : V → V be a variable-renaming function. Given a graph pattern P, a
    copy pattern φ(P) is an isomorphic copy of P whose variables have been renamed
    according to φ and satisfying that var(P) ∩ var(φ(P)) = ∅."    
    
    varExprs maps variable expressions to variables
    vars     maps variables to variables 
    
    """
    from telescope.sparql.helpers import v
    vars={}
    varExprs={}
    copyPatterns=[]
    for formula in toDo:
        for var in GetVars(formula):
            if not var in vars:
                newVar=Variable(BNode())
                varExprs[v[var]]=newVar
                vars[var]=newVar
        copyTriplePattern=copy.deepcopy(formula)
        copyTriplePattern.renameVariables(vars)
        copyPatterns.append(copyTriplePattern)
    return copyPatterns,vars,varExprs
            
def StratifiedSPARQL(rule,nsMapping={EX_NS: 'ex'}):
    """
    The SPARQL specification indicates that it is possible to test if a graph
    pattern does not match a dataset, via a combination of optional patterns and
    filter conditions (like negation as failure in logic programming)([9] Sec. 11.4.1).
    In this section we analyze in depth the scope and limitations of this approach.
    We will introduce a syntax for the “difference” of two graph patterns P1 and
    P2, denoted (P1 MINUS P2), with the intended informal meaning: “the set of
    mappings that match P1 and does not match P2”. 
    
    Uses telescope to construct the SPARQL MINUS BGP expressions for body 
    conditions with default negation formulae              
    """
    from FuXi.Rete.SidewaysInformationPassing import GetArgs, findFullSip, iterCondition
    #Find a sip order of the horn rule
    if isinstance(rule.formula.body,And):
        sipOrder=first(findFullSip(([rule.formula.head],None), rule.formula.body))
    else:
        sipOrder=[rule.formula.head]+[rule.formula.body]
    from telescope import optional, op
    from telescope.sparql.queryforms import Select
    # from telescope.sparql.expressions import Expression
    from telescope.sparql.compiler import SelectCompiler
    from telescope.sparql.patterns import GroupGraphPattern 
    toDo=[]
    negativeVars=set()
    positiveLiterals = False
    for atom in sipOrder[1:]:
        if atom.naf:
            toDo.append(atom)
            negativeVars.update(GetVars(atom))
        else:
            positiveLiterals = True
    #The negative literas are moved to the back of the body conjunct
    #Intuitively, they should not be disconnected from the rest of rule
    #Due to the correlation between DL and guarded FOL
    [sipOrder.remove(toRemove) for toRemove in toDo]
    
    #posLiterals are all the positive literals leading up to the negated
    #literals (in left-to-right order)  There may be none, see below
    posLiterals=sipOrder[1:]    
    
    posVarIgnore = []
    if not positiveLiterals:
        #If there are no lead, positive literals (i.e. the LP is of the form:
        #   H :- not B1, not B2, ...
        #Then a 'phantom' triple pattern is needed as the left operand to the OPTIONAL
        #in order to properly implement P0 MINUS P where P0 is an empty pattern
        keyVar = GetVars(rule.formula.head)[0]
        newVar1=Variable(BNode())
        newVar2=Variable(BNode())
        posVarIgnore.extend([newVar1,newVar2])
        phantomLiteral=Uniterm(newVar1,[keyVar,newVar2])    
        posLiterals.insert(0,phantomLiteral)
            
    #The positive variables are collected
    positiveVars=set(reduce(lambda x,y:x+y,[GetVars(atom) for atom in posLiterals]))

    # vars={}
    # varExprs={}
    # copyPatterns=[]
    print >> sys.stderr, "%s =: { %s MINUS %s} "%(rule.formula.head,
                                                  posLiterals,
                                                  toDo)
    def collapseMINUS(left,right):
        negVars=set()
        for pred in iterCondition(right):
            negVars.update([term for term in GetArgs(pred) 
                                    if isinstance(term,Variable)])
        innerCopyPatternNeeded = not negVars.difference(positiveVars)
        #A copy pattern is needed if the negative literals don't introduce new vars
        if innerCopyPatternNeeded:
            innerCopyPatterns,innerVars,innerVarExprs=createCopyPattern([right])
            #We use an arbitrary new variable as for the outer FILTER(!BOUND(..))
            outerFilterVariable=innerVars.values()[0]
            optionalPatterns=[right] +innerCopyPatterns
            negatedBGP=optional(*[formula.toRDFTuple() 
                                for formula in optionalPatterns])
            negatedBGP.filter(*[k==v for k,v in innerVarExprs.items()])         
            positiveVars.update([Variable(k.value[0:]) for k in innerVarExprs.keys()])
            positiveVars.update(innerVarExprs.values())   
        else:
            #We use an arbitrary, 'independent' variable for the outer FILTER(!BOUND(..))
            outerFilterVariable=negVars.difference(positiveVars).pop()
            optionalPatterns=[right]
            negatedBGP=optional(*[formula.toRDFTuple() 
                                for formula in optionalPatterns])
            positiveVars.update(negVars)
        left=left.where(*[negatedBGP])
        left=left.filter(~op.bound(outerFilterVariable))
        return left        
    topLevelQuery = Select(GetArgs(rule.formula.head)).where(
                             GroupGraphPattern.from_obj([
                                 formula.toRDFTuple() 
                                    for formula in posLiterals]))
    rt=reduce(collapseMINUS,[topLevelQuery]+toDo)
    return rt,SelectCompiler(nsMapping)

def ProperSipOrderWithNegation(body):
    """
    Ensures the list of literals has the negated literals
    at the end of the list
    """
    # from FuXi.Rete.SidewaysInformationPassing import iterCondition
    #import pdb;pdb.set_trace()
    firstNegLiteral = None
    bodyIterator = list(body)
    for idx,literal in enumerate(bodyIterator):
        if literal.naf:
            firstNegLiteral = literal
            break
    if firstNegLiteral:
        #There is a first negative literal, are there subsequent positive literals?
        subsequentPosLits =  first(itertools.dropwhile(lambda i:i.naf,
                                                       bodyIterator[idx:]))
        if len(body) - idx > 1:
            #if this is not the last term in the body
            #then we succeed only if there are no subsequent positive literals
            return not subsequentPosLits 
        else:
            #this is the last term, so we are successful
            return True
    else:
        #There are no negative literals
        return True

class UniversalRestrictionTest(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
                
    def testNegatedDisjunctionTest(self):
        contains=Property(EX_NS.contains)
        omega = EX.Omega
        alpha = EX.Alpha
        innerDisjunct = omega | alpha
        foo = EX.foo
        testClass1 = foo & (contains|only|~innerDisjunct)
        testClass1.identifier = EX_NS.Bar
        
        self.assertEqual(repr(testClass1),
                "ex:foo that ( ex:contains only ( not ( ex:Omega or ex:Alpha ) ) )")
        NormalFormReduction(self.ontGraph)
        self.assertEqual(repr(testClass1),
                "ex:foo that ( not ( ex:contains some ( ex:Omega or ex:Alpha ) ) )")
        
        individual1 = BNode()
        individual2 = BNode()
        foo.extent = [individual1]
        contains.extent = [(individual1,individual2)]
        (EX.Baz).extent = [individual2]
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        posRules,ignored=CalculateStratifiedModel(network,self.ontGraph,[EX_NS.Bar])
        self.failUnless(not posRules,"There should be no rules in the 0 strata!")
        self.assertEqual(len(ignored),2,"There should be 2 'negative' rules")
        testClass1.graph = network.inferredFacts 
        self.failUnless(individual1 in testClass1.extent,
                        "%s should be in ex:Bar's extent"%individual1)        

    def testNominalPartition(self):
        partition = EnumeratedClass(EX_NS.part,
                                    members=[EX_NS.individual1,
                                             EX_NS.individual2,
                                             EX_NS.individual3])
        subPartition = EnumeratedClass(members=[EX_NS.individual1])
        partitionProp = Property(EX_NS.propFoo,
                                 range=partition.identifier)
        self.testClass = (EX.Bar) & (partitionProp|only|subPartition)
        self.testClass.identifier = EX_NS.Foo         
        self.assertEqual(repr(self.testClass),
                        "ex:Bar that ( ex:propFoo only { ex:individual1 } )")        
        self.assertEqual(repr(self.testClass.identifier),
                        "rdflib.term.URIRef('http://example.com/Foo')")        
        NormalFormReduction(self.ontGraph)
        self.assertEqual(repr(self.testClass),
        "ex:Bar that ( not ( ex:propFoo value ex:individual2 ) ) and ( not ( ex:propFoo value ex:individual3 ) )")
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        
        ex = BNode()
        (EX.Bar).extent = [ex]
        self.ontGraph.add((ex,EX_NS.propFoo,EX_NS.individual1))
        CalculateStratifiedModel(network,self.ontGraph,[EX_NS.Foo])
        self.failUnless((ex,RDF.type,EX_NS.Foo) in network.inferredFacts,
                        "Missing level 1 predicate (ex:Foo)")

class NegatedExistentialRestrictionTest(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
                
    def testInConjunct(self):
        contains=Property(EX_NS.contains)
        testCase2 = EX.Operation & ~ (contains|some|EX.IsolatedCABGConcomitantExclusion) &\
                                          (contains|some|EX.CoronaryArteryBypassGrafting)
        testCase2.identifier = EX_NS.IsolatedCABGOperation        
        NormalFormReduction(self.ontGraph)
        self.assertEqual(repr(testCase2),
                        "ex:Operation that ( ex:contains some ex:CoronaryArteryBypassGrafting ) and ( not ( ex:contains some ex:IsolatedCABGConcomitantExclusion ) )")
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        op=BNode()
        (EX.Operation).extent = [op]
        grafting=BNode()
        (EX.CoronaryArteryBypassGrafting).extent = [grafting]
        testCase2.graph.add((op,EX_NS.contains,grafting))        
        CalculateStratifiedModel(network,testCase2.graph,[EX_NS.Foo,EX_NS.IsolatedCABGOperation])
        testCase2.graph = network.inferredFacts 
        self.failUnless(op in testCase2.extent,
                        "%s should be in ex:IsolatedCABGOperation's extent"%op)        
        

    def testGeneralConceptInclusion(self):
#        Some Class 
#            ## Primitive Type  ##
#            SubClassOf: Class: ex:NoExclusion  . 
#            DisjointWith ( ex:contains some ex:IsolatedCABGConcomitantExclusion )
        contains=Property(EX_NS.contains)
        testClass = ~(contains|some|EX.Exclusion)
        testClass2 = EX.NoExclusion
        testClass2 += testClass
        NormalFormReduction(self.ontGraph)
        individual1 = BNode()
        individual2 = BNode()
        contains.extent = [(individual1,individual2)]
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        posRules,negRules=CalculateStratifiedModel(network,self.ontGraph,[EX_NS.NoExclusion])
        self.failUnless(not posRules,"There should be no rules in the 0 strata!")
        self.assertEqual(len(negRules),2,"There should be 2 'negative' rules")
        Individual.factoryGraph = network.inferredFacts
        targetClass = Class(EX_NS.NoExclusion,skipOWLClassMembership=False)
        self.failUnless(individual1 in targetClass.extent,
        "There is a BNode that bears the contains relation with another individual that is not a member of Exclusion!")
        self.assertEquals(len(list(targetClass.extent)),1,
                          "There should only be one member in NoExclusion")

class NegatedDisjunctTest(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
                
    def testStratified(self):
        bar=EX.Bar
        baz=EX.Baz
        noBarOrBaz = ~(bar|baz)
        omega = EX.Omega
        foo = omega & noBarOrBaz
        foo.identifier = EX_NS.Foo
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        individual=BNode()
        omega.extent = [individual]
        NormalFormReduction(self.ontGraph)
        self.assertEqual(repr(foo),
                         "ex:Omega that ( not ex:Bar ) and ( not ex:Baz )")
        posRules,negRules=CalculateStratifiedModel(network,self.ontGraph,[EX_NS.Foo])
        foo.graph = network.inferredFacts
        self.failUnless(not posRules,"There should be no rules in the 0 strata!")
        self.assertEqual(repr(negRules[0]),"Forall ?X ( ex:Foo(?X) :- And( ex:Omega(?X) not ex:Bar(?X) not ex:Baz(?X) ) )")
        self.failUnless(len(negRules)==1,"There should only be one negative rule in a higher strata")
        self.failUnless(individual in foo.extent,
                        "%s should be a member of ex:Foo"%individual)

class NegationOfAtomicConcept(unittest.TestCase):
    def setUp(self):
        self.ontGraph = Graph()
        self.ontGraph.bind('ex', EX_NS)
        self.ontGraph.bind('owl', OWL_NS)
        Individual.factoryGraph = self.ontGraph
                
    def testAtomicNegation(self):
        bar=EX.Bar
        baz=~bar
        baz.identifier = EX_NS.Baz
        ruleStore,ruleGraph,network=SetupRuleStore(makeNetwork=True)
        individual=BNode()
        individual2=BNode()
        (EX.OtherClass).extent = [individual]
        bar.extent = [individual2]
        NormalFormReduction(self.ontGraph)
        self.assertEqual(repr(baz),
                         "Class: ex:Baz DisjointWith ex:Bar\n")
        posRules,negRules=CalculateStratifiedModel(network,self.ontGraph,[EX_NS.Foo])
        self.failUnless(not posRules,"There should be no rules in the 0 strata!")
        self.failUnless(len(negRules)==1,"There should only be one negative rule in a higher strata")
        self.assertEqual(repr(negRules[0]),
                         "Forall ?X ( ex:Baz(?X) :- not ex:Bar(?X) )")        
        baz.graph = network.inferredFacts
        self.failUnless(individual in baz.extent,
                        "%s should be a member of ex:Baz"%individual)
        self.failUnless(individual2 not in baz.extent,
                        "%s should *not* be a member of ex:Baz"%individual2)
        
if __name__ == '__main__':
    unittest.main()
