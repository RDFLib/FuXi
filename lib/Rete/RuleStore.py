from __future__ import generators
import sys
from rdflib import Namespace, RDF, BNode, Literal, URIRef, Variable
from rdflib.store import Store,VALID_STORE, CORRUPTED_STORE, NO_STORE, UNKNOWN
try:
    from rdflib.graph import QuotedGraph, Graph
    from rdflib.namespace import NamespaceManager
    from rdfextras.utils.termutils import *
    from rdfextras.store.REGEXMatching import REGEXTerm, NATIVE_REGEX, PYTHON_REGEX
except ImportError:
    from rdflib.Graph import QuotedGraph, Graph
    from rdflib.syntax.NamespaceManager import NamespaceManager
    from rdflib.term_utils import *
    from rdflib.store.REGEXMatching import REGEXTerm, NATIVE_REGEX, PYTHON_REGEX

from pprint import pprint
from cStringIO import StringIO

from BuiltinPredicates import FILTERS

LOG = Namespace("http://www.w3.org/2000/10/swap/log#")
Any = None

RULE_LHS = 0
RULE_RHS = 1

class N3Builtin(object):
    """
    An binary N3 Filter: A built-in which evaluates to a boolean
    """
    def __init__(self,uri,func,argument,result):
        self.uri = uri
        self.argument = argument
        self.result = result
        self.func = func
        self.variables = [arg for arg in [self.argument,self.result] if isinstance(arg,Variable)]

    def isSecondOrder(self):
        return False
        
    def ground(self,varMapping):
        appliedKeys = set([self.argument,self.result]).intersection(varMapping.keys())
        self.argument = varMapping.get(self.argument,self.argument)
        self.result   = varMapping.get(self.result,self.result)
        return appliedKeys
        
    def isGround(self):
        for term in [self.result,self.argument]:
            if isinstance(term,Variable):
                return False
        return True

    def renameVariables(self,varMapping):
        if varMapping:
            self.argument=varMapping.get(self.argument,self.argument)
            self.result  =varMapping.get(self.result  ,self.result)
        
    def binds(self,var):
        return True
    
    def toRDFTuple(self):
        return (self.argument,self.uri,self.result)
    def render(self,argument,result):
        return "<%s>(%s,%s)"%(self.uri,argument,result)
    def __iter__(self):
        for f in [self.uri,self.argument,self.result]:
            yield f
    
    def __repr__(self):
        return "<%s>(%s,%s)"%(self.uri,
                              isinstance(self.argument,Variable) and '?%s'%self.argument or self.argument,
                              isinstance(self.result,Variable) and '?%s'%self.result or self.result)
                              
class Formula(object):
    """
    An N3 Formula.  Consists of an (internal) identifier
    and a *list* of triples
    """
    def __init__(self,identifier):
        self.identifier = identifier
        self.triples = []
    def __len__(self):
        return len(self.triples)
    def __repr__(self):
        return "{%s}"%(repr(self.triples))
    def __getitem__(self, key):
        return self.triples[key]
    def __iter__(self):
        for item in self.triples:
            yield item
    def extend(self,other):
        self.triples.extend(other)
    def append(self,other):
        self.triples.append(other)

class Rule(object):
    """
    An N3 Rule.  consists of two formulae associated via log:implies
    """
    def __init__(self,LHS,RHS):
        self.lhs = LHS
        self.rhs = RHS

    def __repr__(self):
        return "{%s} => {%s}"%(self.lhs,self.rhs)

def SetupRuleStore(n3Stream=None,additionalBuiltins=None,makeNetwork=False):
    """
    Sets up a N3RuleStore, a Graph (that uses it as a store, and )
    """
    ruleStore = N3RuleStore(additionalBuiltins=additionalBuiltins)
    nsMgr = NamespaceManager(Graph(ruleStore))
    ruleGraph = Graph(ruleStore,namespace_manager=nsMgr)            
    if n3Stream:
        ruleGraph.parse(n3Stream,format='n3')
    if makeNetwork:
        from Network import ReteNetwork
        closureDeltaGraph = Graph()
        network = ReteNetwork(ruleStore,inferredTarget = closureDeltaGraph)        
        return ruleStore,ruleGraph,network
    return ruleStore,ruleGraph
        
class N3RuleStore(Store):
    """    
    A specialized Store which maintains order of statements
    and creates N3Filters, Rules, Formula objects, and other facts
    Ensures builtin filters refer to variables that have preceded

    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... @prefix str:   <http://www.w3.org/2000/10/swap/string#>.
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix log:   <http://www.w3.org/2000/10/swap/log#>.
    ... @prefix m: <http://metacognition.info/FuXi/test#>.
    ... @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    ... @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    ... @prefix owl: <http://www.w3.org/2002/07/owl#>.    
    ... m:a a rdfs:Class;
    ...    m:prop1 1;
    ...    m:prop2 4.
    ... m:b a owl:Class;
    ...    m:prop1 2;
    ...    m:prop2 4,1,5.
    ... (1 2) :relatedTo (3 4).
    ... { ?X a owl:Class. ?X :prop1 ?M. ?X :prop2 ?N. ?N math:equalTo 3 } => { [] :selected (?M ?N) }.\"\"\"    
    >>> g=g.parse(StringIO(src),format='n3')
    >>> s._finalize()
    >>> len([pred for subj,pred,obj in s.facts if pred == u'http://metacognition.info/FuXi/test#relatedTo'])
    1
    >>> len(s.rules)
    1
    >>> print len(s.rules[0][RULE_LHS])
    4
    >>> print len(s.rules[0][RULE_RHS])
    5
    >>> print s.rules[0][RULE_LHS][1]
    (?X, rdflib.URIRef('http://metacognition.info/FuXi/test#prop1'), ?M)
    >>> print s.rules[0][RULE_LHS][-1]
    <http://www.w3.org/2000/10/swap/math#equalTo>(?N,3)

Description Rule Patterns Compilation
    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    ... @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    ... @prefix owl: <http://www.w3.org/2002/07/owl#>. 
    ... { ?S a [ rdfs:subClassOf ?C ] } => { ?S a ?C }.\"\"\"
    >>> g=g.parse(StringIO(src),format='n3')
    >>> s._finalize()
    >>> assert s.rules
    >>> assert [pattern for pattern in s.rules[0][RULE_LHS] if isinstance(pattern,tuple) and [term for term in pattern if isinstance(term,BNode) ]],repr(s.rules[0][RULE_LHS])    


Test single fact with collection

    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    ... @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    ... @prefix owl: <http://www.w3.org/2002/07/owl#>.    
    ... (1 2) :relatedTo owl:Class.\"\"\"    
    >>> g=g.parse(StringIO(src),format='n3')
    >>> s._finalize()
    >>> print len(s.facts)
    5

RHS can only include RDF triples

    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    ... @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    ... @prefix owl: <http://www.w3.org/2002/07/owl#>.    
    ... {} => { 3 math:lessThan 2}.\"\"\"    
    >>> g=g.parse(StringIO(src),format='n3')
    >>> try: 
    ...   s._finalize()
    ... except Exception,e:
    ...   print e
    Rule RHS must only include RDF triples! (<http://www.w3.org/2000/10/swap/math#lessThan>(3,2))

BuiltIn used out of order

    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... { ?M math:lessThan ?Z.  ?R :value ?M; :value2 ?Z} => { ?R a :Selected.  }.\"\"\"    
    >>> try: 
    ...   g=g.parse(StringIO(src),format='n3')
    ... except Exception,e:
    ...   print e
    Builtin refers to variables without previous reference! (<http://www.w3.org/2000/10/swap/math#lessThan>(?M,?Z))

    Empty LHS & RHS
    >>> s=N3RuleStore()
    >>> g=Graph(s)
    >>> src = \"\"\"
    ... @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    ... @prefix : <http://metacognition.info/FuXi/test#>.
    ... @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    ... @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    ... @prefix owl: <http://www.w3.org/2002/07/owl#>.    
    ... {} => {rdf:nil :allClasses ?C}.
    ... {?C owl:oneOf ?L. ?X a ?C. ?L :notItem ?X} => {}.\"\"\"    
    >>> g=g.parse(StringIO(src),format='n3')
    >>> len(s.formulae)
    2
    >>> s._finalize()
    >>> len(s.rules[0][0])
    0
    >>> len(s.rules[1][-1])
    0
    """
    context_aware = True
    formula_aware = True

    def __init__(self, identifier=None, additionalBuiltins=None):
        self.formulae = {}
        self.facts = []
        self.rootFormula = None
        self._lists = {}
        self.currentList = None
        self._listBuffer = []
        self.rules = []
        self.referencedVariables = set()
        self.nsMgr = {u'skolem':URIRef('http://code.google.com/p/python-dlp/wiki/SkolemTerm#')}
        self.filters={}
        self.filters.update(FILTERS)
        if additionalBuiltins:
            self.filters.update(additionalBuiltins)
        
    def namespace(self,prefix):
        return self.nsMgr.get(prefix)
    
    def bind(self, prefix, namespace, override=True):
        if override or prefix not in self.nsMgr:
            self.nsMgr[prefix]=namespace

    def prefix(self,namespace):
        return dict([(v,k) for 
                       k,v in self.nsMgr.items()]).get(namespace)
        
    def _unrollList(self,l,listName):
        listTriples = []
        lastItemName = None
        for linkItem in l:
            linkName = l.index(linkItem) == 0 and listName or BNode()
            if lastItemName:
                listTriples.append((lastItemName,RDF.rest,linkName))
            listTriples.append((linkName,RDF.first,linkItem))
            lastItemName = linkName
        listTriples.append((lastItemName,RDF.rest,RDF.nil))
        return listTriples 
        
    def _finalize(self):        
        def unrollFunc(left,right):            
            leftListsToUnroll = []
            rightListsToUnroll = []
            if isinstance(left,tuple):
                s,p,o = left
                leftListsToUnroll = [term for term in [s,o] if term in self._lists]
                if leftListsToUnroll:
                    leftListsToUnroll = reduce(lambda x,y:x+y,[self._unrollList(self._lists[l],l) for l in leftListsToUnroll]) 
                left = [left]
            elif isinstance(left,N3Builtin):
                left = [left]
            if isinstance(right,tuple):
                s,p,o = right
                rightListsToUnroll = [term for term in [s,o] if term in self._lists]
                if rightListsToUnroll:
                    rightListsToUnroll = reduce(lambda x,y:x+y,[self._unrollList(self._lists[l],l) for l in rightListsToUnroll])
                right = [right]
            elif isinstance(right,N3Builtin):
                right = [right]                    
            return left +leftListsToUnroll+right+rightListsToUnroll
        if len(self.facts) == 1:
            s,p,o = self.facts[0]
            listsToUnroll = [term for term in [s,o] if term in self._lists]
            if listsToUnroll:
                self.facts.extend(reduce(lambda x,y:x+y,[self._unrollList(self._lists[l],l) for l in listsToUnroll]))            
        elif self.facts:
            self.facts = reduce(unrollFunc,self.facts)
        for formula in self.formulae.values():
            if len(formula) == 1:
                if isinstance(formula[0],tuple):
                    s,p,o = formula[0]
                    listsToUnroll = [term for term in [s,o] if term in self._lists]
                    if listsToUnroll:
                        listTriples = reduce(lambda x,y:x+y,[self._unrollList(self._lists[l],l) for l in listsToUnroll])
                        formula.extend(listTriples)
            elif len(formula):            
                formula.triples = reduce(unrollFunc,[i for i in formula])
        for lhs,rhs in self.rules:
            for item in self.formulae.get(rhs,[]):
                assert isinstance(item,tuple),"Rule RHS must only include RDF triples! (%s)"%item
        self.rules = [(self.formulae.get(lhs,Formula(lhs)),self.formulae.get(rhs,Formula(rhs))) for lhs,rhs in self.rules]
    
    def _checkVariableReferences(self,referencedVariables,terms,funcObj):
        for term in [i for i in terms if isinstance(i,Variable)]:
            if term not in referencedVariables:
                raise Exception("Builtin refers to variables without previous reference! (%s)"%funcObj)
    
    def add(self, (subject, predicate, obj), context=None, quoted=False):
        if predicate == RDF.first and not isinstance(subject,Variable) and not isinstance(object,Variable):
            if not self.currentList:
                self._listBuffer.append(obj)
                self.currentList = subject
            else:
                self._listBuffer.append(obj)
        elif predicate == RDF.rest and not isinstance(subject,Variable) and not isinstance(object,Variable):
            if obj == RDF.nil:
                self._lists[self.currentList] = [item for item in self._listBuffer]
                self._listBuffer = []
                self.currentList = None
        elif not isinstance(context,QuotedGraph):
            if not self.rootFormula:
                self.rootFormula = context.identifier
            if predicate == LOG.implies:
                self.rules.append(
                      (isinstance(subject,URIRef) and subject or subject.identifier,
                       isinstance(obj,URIRef) and obj or obj.identifier))
            else:                
                self.facts.append((subject,predicate,obj))
        else:
            formula = self.formulae.get(context.identifier,Formula(context.identifier))
            if predicate in self.filters:
                newFilter = N3Builtin(predicate,self.filters[predicate](subject,obj),subject,obj)
                #@attention: The non-deterministic parse order of an RDF graph makes this
                #check hard to enforce
                #self._checkVariableReferences(self.referencedVariables,[subject,obj],newFilter)
                formula.append(newFilter)
            else:
                #print "(%s,%s,%s) pattern in %s"%(subject,predicate,obj,context.identifier)
                variables = [arg for arg in [subject,predicate,obj] if isinstance(arg,Variable)]
                self.referencedVariables.update(variables)
                formula.append((subject,predicate,obj))
            self.formulae[context.identifier] = formula
                
    def __repr__(self):
        return ""
    
    def __len__(self, context=None):
        return 0
    
    def optimizeRules(self):
        patternDict = {}
        for lhs,rhs in self.rules:
            for pattern in lhs:
                if not isinstance(pattern,N3Builtin):
                    _hashList = [isinstance(term,(Variable,BNode)) and '\t' or term for term in pattern]
                    patternDict.setdefault(reduce(lambda x,y:x+y,_hashList),set()).add(pattern)
        for key,vals in patternDict.items():
            if len(vals) > 1:
                print "###### Similar Patterns ######"
                for val in vals:
                    print val 
                print "##############################"
    
def test():
    import doctest
    doctest.testmod()

def test2():
    s=N3RuleStore()
    g=Graph(s)
    src = """
    @prefix math: <http://www.w3.org/2000/10/swap/math#>.
    @prefix : <http://metacognition.info/FuXi/test#>.
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
    @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.
    @prefix owl: <http://www.w3.org/2002/07/owl#>.
    :subj :pred obj.     
    {} => { 3 math:lessThan 2}."""    
    g=g.parse(StringIO(src),format='n3')
    s._finalize()

if __name__ == '__main__':
#    pass
    test()
    #test2()
