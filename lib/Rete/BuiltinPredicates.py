"""
See: http://www.w3.org/2000/10/swap/doc/CwmBuiltins
"""
import unittest, os, time, sys
from cStringIO import StringIO
from rdflib import Namespace, Variable, Literal, URIRef
from rdflib.Graph import Graph,ReadOnlyGraphAggregate,ConjunctiveGraph
from rdflib.util import first
STRING_NS = Namespace("http://www.w3.org/2000/10/swap/string#")
LOG_NS = Namespace("http://www.w3.org/2000/10/swap/log#")
MATH_NS = Namespace("http://www.w3.org/2000/10/swap/math#")
EULER_NS = Namespace("http://eulersharp.sourceforge.net/2003/03swap/owl-rules#")

def LogNotEqualTo(subject,object_):
    """
    Equality in this sense is actually the same URI.      
    """
    def func(s,o):
        return s != o
    return func

def LogEqualTo(subject,object_):
    """
    True if the subject and object are the same RDF node (symbol or literal).
    """
    def func(s,o):
        return s == o
    return func

def StringContains(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"str:greaterThan can only be used with Literals! (%s)"%term
    def containsF(s,o):
        return s[-1].contains(o[-1])
    return containsF

def StringGreaterThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"str:greaterThan can only be used with Literals! (%s)"%term
    def greaterThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"str:greaterThan can only be used with Literals!: %s %s"%(s,o)
        return str(s) > str(o)
    return greaterThanF

def StringLessThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"str:lessThan can only be used with Literals! (%s)"%term
    def lessThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"str:lessThan can only be used with Literals!"
        return s < o
        #return str(s) < str(o)
    return lessThanF

def StringEqualIgnoringCase(subject,object_):
    pass

#def MathProduct(arguments):
#    def productF(bindings):
#        return eval(' * '.join([isinstance(arg,Variable) and 'bindings[u"%s"]'%arg or str(arg) for arg in arguments]))
#    return productF
def MathEqualTo(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:equalTo can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:equalTo can only be used with Numeric Literals! (%s)"%term    
    def func(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:equalTo can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:equalTo can only be used with Numeric Literals!"
        return s.toPython() == o.toPython()
    return func
def MathGreaterThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def greaterThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:greaterThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:greaterThan can only be used with Numeric Literals!"
        return s.toPython() > o.toPython()
    return greaterThanF

def MathLessThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def lessThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:lessThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals!"
        return s.toPython() < o.toPython()
    return lessThanF

def MathNotLessThan(subject,object_):
    for term in [subject,object_]:
        if not isinstance(term,Variable):
            assert isinstance(term,Literal),"math:notLessThan can only be used with Literals! (%s)"%term
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals! (%s)"%term    
    def nLessThanF(s,o):
        for term in [s,o]:
            assert isinstance(term,Literal),"math:notLessThan can only be used with Literals!"
            assert isinstance(term.toPython(),(int,float,long)),"math:lessThan can only be used with Numeric Literals!"
        return not(s.toPython() < o.toPython())
    return nLessThanF

FUNCTIONS = {
}
FILTERS = {
    LOG_NS.equalTo : LogEqualTo,
    LOG_NS.includes : None,
    LOG_NS.notEqualTo : LogNotEqualTo,
    LOG_NS.notIncludes : None,
    MATH_NS.equalTo : MathEqualTo,
    MATH_NS.greaterThan : MathGreaterThan,
    MATH_NS.lessThan : MathLessThan,
    MATH_NS.notEqualTo : None,
    MATH_NS.notGreaterThan : None,
    MATH_NS.notLessThan : MathNotLessThan,
    STRING_NS.contains : StringContains,
    STRING_NS.containsIgnoringCase : None,
    STRING_NS.endsWith : None,
    STRING_NS.equalIgnoringCase : StringEqualIgnoringCase,
    STRING_NS.greaterThan : StringGreaterThan,
    STRING_NS.lessThan : StringLessThan,
    STRING_NS.matches : None,
    STRING_NS.notEqualIgnoringCase : None,
    STRING_NS.notGreaterThan : None,
    STRING_NS.notLessThan : None,
    STRING_NS.notMatches : None,
    STRING_NS.startsWith : None,    
}

testN3="""
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix : <http://test/> .
@prefix math: <http://www.w3.org/2000/10/swap/math#> .
{ ?NODE rdf:value ?VAL. ?VAL math:greaterThan 2} => {?NODE :pred1 ?VAL}.
_:foo rdf:value 1;
      rdf:value 2;
      rdf:value 3.
"""

class NonEqualityPredicatesTestSuite(unittest.TestCase):
    def setUp(self):
        from FuXi.Rete.RuleStore import N3RuleStore
        from FuXi.Rete import ReteNetwork
        from FuXi.Rete.Util import generateTokenSet
        self.testGraph = Graph()
        self.ruleStore=N3RuleStore()
        self.ruleGraph = Graph(self.ruleStore)           
        self.ruleGraph.parse(StringIO(testN3),format='n3')
        self.testGraph.parse(StringIO(testN3),format='n3')        
        self.closureDeltaGraph = Graph()
        self.network = ReteNetwork(self.ruleStore,
                                   initialWorkingMemory=generateTokenSet(self.testGraph),
                                   inferredTarget = self.closureDeltaGraph,
                                   nsMap = {})
    def testParseBuiltIns(self):
        from FuXi.Rete.RuleStore import N3Builtin
        from FuXi.Rete.AlphaNode import BuiltInAlphaNode
        self.failUnless(self.ruleStore.rules>0, "No rules parsed out form N3!")
        for alphaNode in self.network.alphaNodes:
            if isinstance(alphaNode, BuiltInAlphaNode):
                self.failUnless(alphaNode.n3builtin.uri == MATH_NS.greaterThan, 
                                "Unable to find math:greaterThan func")

    def testEvaluateBuiltIns(self):
        from FuXi.Rete.RuleStore import N3Builtin
        from FuXi.Rete.AlphaNode import BuiltInAlphaNode
        self.failUnless(first(self.closureDeltaGraph.triples((None,URIRef('http://test/pred1'),Literal(3)))),
                            "Missing inferred :pred1 assertions")
    
if __name__ == '__main__':
    unittest.main()    
