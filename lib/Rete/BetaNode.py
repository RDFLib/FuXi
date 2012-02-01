"""
Implements the behavior associated with the 'join' (Beta) node in a RETE network:
    - Stores tokens in two memories
    - Tokens in memories are checked for consistent bindings (unification) for variables in common *across* both
    - Network 'trigger' is propagated downward
    
This reference implementation follows,  quite closely, the algorithms presented in the PhD thesis (1995) of Robert Doorenbos:
    Production Matching for Large Learning Systems (RETE/UL)
    
A N3 Triple is a working memory element (WME)

The Memories are implemented with consistent binding hashes. Unlinking is not implemented but null 
activations are mitigated (somewhat) by the hash / Set mechanism.
              
"""
import unittest, copy
from itertools import izip, ifilter
from pprint import pprint
from AlphaNode import AlphaNode, BuiltInAlphaNode, ReteToken
from Node import Node
from RuleStore import N3Builtin
from IteratorAlgebra import hash_join
from Util import xcombine
try:
    set
except NameError:
    from sets import Set as set
from itertools import izip
from ReteVocabulary import RETE_NS

try:
    from rdflib.graph import QuotedGraph, Graph
    from rdflib.collection import Collection
except ImportError:
    from rdflib.Graph import QuotedGraph, Graph
    from rdflib.Collection import Collection
from rdflib import Variable, Literal, URIRef, BNode, Namespace, RDF, RDFS
_XSD_NS = Namespace('http://www.w3.org/2001/XMLSchema#')
OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")
Any = None

LEFT_MEMORY  = 1
RIGHT_MEMORY = 2

#Implementn left unlinking?
LEFT_UNLINKING = False

memoryPosition = {
    LEFT_MEMORY : "left",
    RIGHT_MEMORY: "right",
}

def collectVariables(node):
    """
    Utility function for locating variables common to the patterns in both left and right nodes
    """
    if isinstance(node,BuiltInAlphaNode):
        return set()
    if isinstance(node,AlphaNode):
        return set([term for term in node.triplePattern if isinstance(term,(Variable,BNode))])
    elif node:
        combinedVars = set()
        combinedVars |= node.leftVariables
        combinedVars |= node.rightVariables
        return combinedVars
    else:
        return set()
        
#From itertools recipes
def iteritems(mapping): 
    return izip(mapping.iterkeys(),mapping.itervalues())
    
def any(seq,pred=None):
    """Returns True if pred(x) is true for at least one element in the iterable"""
    for elem in ifilter(pred,seq):
        return True
    return False

class ReteMemory(set):
    def __init__(self,betaNode,position,filter=None):
        super(ReteMemory, self).__init__(())
        self.filter                = filter
        self.successor             = betaNode
        self.position              = position
        self.substitutionDict      = {} #hashed 
        
    def union(self, other):
        """Return the union of two sets as a new set.

        (I.e. all elements that are in either set.)
        """
        result = ReteMemory(self.successor,self.position)
        result.update(other)
        return result    

    def __repr__(self):
        return "<%sMemory: %s item(s)>"%(self.position == LEFT_MEMORY and 'Beta' or 'Alpha', len(self))

    def addToken(self,token,debug=False):
        commonVarKey = []
        if isinstance(token,PartialInstantiation):
            for binding in token.bindings:
                commonVarKey = []
                for var in self.successor.commonVariables:
                    commonVarKey.append(binding.get(var))
                self.substitutionDict.setdefault(tuple(commonVarKey),set()).add(token)
        else:
            for var in self.successor.commonVariables:            
                commonVarKey.append(token.bindingDict.get(var))        
            self.substitutionDict.setdefault(tuple(commonVarKey),set()).add(token)
        self.add(token)

    def reset(self):
        self.clear()
        self.substitutionDict = {}
        
    @classmethod
    def _wrap_methods(cls, names):
        def wrap_method_closure(name):
            def inner(self, *args):
                result = getattr(super(cls, self), name)(*args)
                if isinstance(result, set) and not hasattr(result, 'foo'):
                    result = cls(result, foo=self.foo)
                return result
            inner.fn_name = name
            setattr(cls, name, inner)
        for name in names:
            wrap_method_closure(name)

ReteMemory._wrap_methods(['__ror__', 'difference_update', '__isub__', 
    'symmetric_difference', '__rsub__', '__and__', '__rand__', 'intersection',
    'difference', '__iand__', '__ixor__', 
    'symmetric_difference_update', '__or__', 'copy', '__rxor__',
    'intersection_update', '__xor__', '__ior__', '__sub__',
])

def project(orig_dict, attributes,inverse=False):
    """
    Dictionary projection: http://jtauber.com/blog/2005/11/17/relational_python:_projection
    
    >>> a = {'one' : 1, 'two' : 2, 'three' : 3 }
    >>> project(a,['one','two'])
    {'two': 2, 'one': 1}
    >>> project(a,['four'])
    {}
    >>> project(a,['one','two'],True)
    {'three': 3}
    """
    if inverse:
        return dict([item for item in orig_dict.items() if item[0] not in attributes])
    else:
        return dict([item for item in orig_dict.items() if item[0] in attributes])
        
class PartialInstantiation(object):
    """
    Represents a set of WMEs 'joined' along one or more
    common variables from an ancestral join node 'up' the network
    
    In the RETE/UL PhD thesis, this is refered to as a token, which contains a set of WME triples.
    This is a bit of a clash with the use of the same word (in the original Forgy paper) to 
    describe what is essentially a WME and whether or not it is an addition to the networks memories 
    or a removal
    
    It is implemented (in the RETE/UL thesis) as a linked list of:
        
    structure token:
        parent: token {points to the higher token, for items 1...i-1} 
        wme: WME {gives item i}
    end
    
    Here it is instead implemented as a Set of WME triples associated with a list variables whose
    bindings are consistent
    
    
    >>> aNode = AlphaNode((Variable('X'),RDF.type,Variable('C')))
    >>> token = ReteToken((URIRef('urn:uuid:Boo'),RDF.type,URIRef('urn:uuid:Foo')))
    >>> token = token.bindVariables(aNode)
    >>> PartialInstantiation([token])    
    <PartialInstantiation: Set([<ReteToken: X->urn:uuid:Boo,C->urn:uuid:Foo>])>
    >>> for token in PartialInstantiation([token]):
    ...   print token
    <ReteToken: X->urn:uuid:Boo,C->urn:uuid:Foo>
    """
    def __init__(self,tokens = None,debug = False,consistentBindings = None):
        """
        Note a hash is calculated by 
        sorting & concatenating the hashes of its tokens 
        """
        self.joinedBindings = consistentBindings and consistentBindings or {}
        self.inconsistentVars = set()
        self.debug = debug
        self.tokens = set()
        self.bindings = []
        if tokens:
            for token in tokens:
                self.add(token,noPostProcessing=True)        
            self._generateHash()
            self._generateBindings()

    def copy(self):
        tokenList = []
        for token in self.tokens:
            wme = copy.deepcopy(token)
            tokenList.append(wme)
        return PartialInstantiation(tokenList,consistentBindings = self.joinedBindings)

    def _generateHash(self):
        tokenHashes = [hash(token) for token in self.tokens]
        tokenHashes.sort()
        self.hash = hash(reduce(lambda x,y:x+y,tokenHashes))        

    def unify(self,left,right):
        """
        Takes two dictionary and collapses it if there are no overlapping 'bindings' or
        'rounds out' both dictionaries so they each have each other's non-overlapping binding 
        """
        bothKeys = [key for key in left.keys() + right.keys() if key not in self.joinedBindings]
        if len(bothKeys) == len(set(bothKeys)):
            joinDict = left.copy()
            joinDict.update(right)
            return joinDict
        else:
            rCopy = right.copy()
            left.update(project(rCopy,[key for key in right.keys() if key not in left]))          
            lCopy = left.copy()
            right.update(project(lCopy,[key for key in left.keys() if key not in right]))
            return [left,right]

    def _generateBindings(self):
        """
        Generates a list of dictionaries - each a unique variable substitution (binding)
        which applies to the ReteTokens in this PartialInstantiation

        Unjoined variables with different names aren't bound to the same value
        (B and Y aren't both bound to "Bart Simpson" simultaneously)
        
        Different variables which bind to the same value *within* a token includes this combination
        in the resulting bindings

        """

        def product(*args):
            if not args:
                return iter(((),)) # yield tuple()
            return (items + (item,)
                    for items in product(*args[:-1]) for item in args[-1])

        disjunctiveDict = {}
        for token in self.tokens:
            for key,val in token.bindingDict.items():
                disjunctiveDict.setdefault(key,set()).add(val)
        keys = list(disjunctiveDict)
        bindings = [dict([(keys[idx],val) for idx,val in enumerate(entry)])
            for entry in product(*tuple([disjunctiveDict[var]
                                         for var in disjunctiveDict]))]
        self.bindings = bindings

    def __hash__(self):
        return self.hash 

    def __eq__(self,other):
        return hash(self) == hash(other)                   

    def add(self,token,noPostProcessing=False):
        """        
        >>> aNode = AlphaNode((Variable('S'),Variable('P'),Variable('O')))
        >>> token1 = ReteToken((URIRef('urn:uuid:Boo'),RDF.type,URIRef('urn:uuid:Foo')))
        >>> token2 = ReteToken((URIRef('urn:uuid:Foo'),RDF.type,URIRef('urn:uuid:Boo')))
        >>> inst = PartialInstantiation([token1.bindVariables(aNode),token2.bindVariables(aNode)])
        >>> inst    
        <PartialInstantiation: Set([<ReteToken: S->urn:uuid:Boo,P->http://www.w3.org/1999/02/22-rdf-syntax-ns#type,O->urn:uuid:Foo>, <ReteToken: S->urn:uuid:Foo,P->http://www.w3.org/1999/02/22-rdf-syntax-ns#type,O->urn:uuid:Boo>])>
        """
        self.tokens.add(token)        
        if not noPostProcessing:
            self._generateHash()
            self._generateBindings()
    
    def __repr__(self):
        if self.joinedBindings:
            joinMsg = ' (joined on %s)'%(','.join(['?'+v for v in self.joinedBindings]))
        else:
            joinMsg = ''
        return "<PartialInstantiation%s: %s>"%(joinMsg,self.tokens)

    def __iter__(self):
        for i in self.tokens:
            yield i
    
    def __len__(self):
        return len(self.tokens)

    def addConsistentBinding(self,newJoinVariables):
        #newJoinDict = self.joinedBindings.copy()
        #only a subset of the tokens in this partial instantiation will be 'merged' with
        #the new token - joined on the new join variables
        newJoinDict = dict([(v,None) for v in newJoinVariables])
        unmappedJoinVars = set(newJoinDict)
        #newJoinDict.update(dict([(v,None) for v in newJoinVariables]))
        for binding in self.bindings:
            for key,val in newJoinDict.iteritems():
                boundVal = binding.get(key)
                if boundVal is not None:
                    unmappedJoinVars.discard(key)
                    if val is None:
                        newJoinDict[key]=boundVal
        if unmappedJoinVars:
            for unmappedVar in unmappedJoinVars:
                for token in self.tokens:
                    unmappedVarVal = token.getVarBindings().get(unmappedVar)
                    if unmappedVarVal is not None:
                        assert newJoinDict[unmappedVar] is None or unmappedVarVal == newJoinDict[unmappedVar]
                        newJoinDict[unmappedVar] = unmappedVarVal
        self.joinedBindings.update(newJoinDict)
        self._generateBindings()             
        
    def newJoin(self,rightWME,newJoinVariables):
        """
        >>> aNode1 = AlphaNode((Variable('P1'),RDF.type,URIRef('urn:uuid:Prop1')))
        >>> aNode2 = AlphaNode((Variable('P2'),RDF.type,URIRef('urn:uuid:Prop1')))
        >>> aNode3 = AlphaNode((Variable('P1'),Variable('P2'),RDFS.Class))
        >>> token1 = ReteToken((RDFS.domain,RDFS.domain,RDFS.Class))
        >>> token2 = ReteToken((RDFS.domain,RDF.type,URIRef('urn:uuid:Prop1')))
        >>> token3 = ReteToken((RDFS.range,RDF.type,URIRef('urn:uuid:Prop1')))
        >>> token4 = ReteToken((RDFS.range,RDFS.domain,RDFS.Class))
        >>> token5 = ReteToken((RDFS.domain,RDF.type,URIRef('urn:uuid:Prop1'))).bindVariables(aNode2)
        >>> inst = PartialInstantiation([token2.bindVariables(aNode1),token3.bindVariables(aNode2),token5])
        >>> pprint(list(inst.tokens))
        [<ReteToken: P2->http://www.w3.org/2000/01/rdf-schema#range>,
         <ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain>,
         <ReteToken: P2->http://www.w3.org/2000/01/rdf-schema#domain>]
        >>> newInst = inst.newJoin(token1.bindVariables(aNode3),[Variable('P2')])
        >>> token1
        <ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain,P2->http://www.w3.org/2000/01/rdf-schema#domain>
        >>> newInst
        <PartialInstantiation (joined on ?P2): Set([<ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain,P2->http://www.w3.org/2000/01/rdf-schema#domain>, <ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain>, <ReteToken: P2->http://www.w3.org/2000/01/rdf-schema#domain>])>
        >>> pprint(list(newInst.tokens))
        [<ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain,P2->http://www.w3.org/2000/01/rdf-schema#domain>,
         <ReteToken: P1->http://www.w3.org/2000/01/rdf-schema#domain>,
         <ReteToken: P2->http://www.w3.org/2000/01/rdf-schema#domain>]
        """
        newJoinDict = self.joinedBindings.copy()
        if newJoinVariables:
            #only a subset of the tokens in this partial instantiation will be 'merged' with
            #the new token - joined on the new join variables
            newJoinDict.update(project(rightWME.bindingDict,newJoinVariables))
            newPInst = PartialInstantiation([],consistentBindings=newJoinDict)
            for token in self.tokens:
                commonVars = False
                for newVar in ifilter(
                    lambda x:x in token.bindingDict and rightWME.bindingDict[x] == token.bindingDict[x],
                    newJoinVariables):
                    #consistent token
                    commonVars = True
                    newPInst.add(token,noPostProcessing=True)
                if not commonVars:
                    #there are no common variables, no need to check
                    newPInst.add(token,noPostProcessing=True)
        else:
            #all of the tokens in this partial instantiation are already bound consistently with
            #respect to the new token
            newPInst = PartialInstantiation([],consistentBindings=newJoinDict)
            for token in self.tokens:
                newPInst.add(token,noPostProcessing=True)
        newPInst.add(rightWME)
        return newPInst            
            
class BetaNode(Node): 
    """
    Performs a rete network join between partial instantiations in its left memory and tokens in its memories

    "The data structure for a join node, therefore, must contain pointers to its two memory
    nodes (so they can be searched), a specification of any variable binding consistency tests to be
    performed, and a list of the node's children. .. (the beta memory is always its parent)."
    
    Setup 3 alpha nodes (Triple Patterns):
        
        aNode1 = ?X rdf:value 1
        aNode2 = ?X rdf:type ?Y
        aNode3 = ?Z <urn:uuid:Prop1> ?W
    
    >>> aNode1 = AlphaNode((Variable('X'),RDF.value,Literal(2)))
    >>> aNode2 = AlphaNode((Variable('X'),RDF.type,Variable('Y')))                            
    >>> aNode3 = AlphaNode((Variable('Z'),URIRef('urn:uuid:Prop1'),Variable('W')))
    

    Rete Network
    ------------

   aNode1 
     |
  joinNode1
       \   aNode2  
        \   /    aNode3
       joinNode2  / 
           \     /
            \   /
         joinNode3    
        
    joinNode3 is the Terminal node
    
    >>> joinNode1 = BetaNode(None,aNode1,aPassThru=True)
    >>> joinNode1.connectIncomingNodes(None,aNode1)
    >>> joinNode2 = BetaNode(joinNode1,aNode2)
    >>> joinNode2.connectIncomingNodes(joinNode1,aNode2)    
    >>> joinNode3 = BetaNode(joinNode2,aNode3)
    >>> joinNode3.connectIncomingNodes(joinNode2,aNode3)

    >>> joinNode1
    <BetaNode (pass-thru): CommonVariables: [?X] (0 in left, 0 in right memories)>
    >>> joinNode2
    <BetaNode : CommonVariables: [?X] (0 in left, 0 in right memories)>

    Setup tokens (RDF triples):
        
        token1 = <urn:uuid:Boo> rdf:value 2
        token2 = <urn:uuid:Foo> rdf:value 2
        token3 = <urn:uuid:Foo> rdf:type <urn:uuid:Baz>             (fires network)
         
        token3 is set with a debug 'trace' so its path through the network is printed along the way
        
        token4 = <urn:uuid:Bash> rdf:type <urn:uuid:Baz>            
        token5 = <urn:uuid:Bar> <urn:uuid:Prop1> <urn:uuid:Beezle>  (fires network)
        token6 = <urn:uuid:Bar> <urn:uuid:Prop1> <urn:uuid:Bundle>  (fires network)

    >>> token1 = ReteToken((URIRef('urn:uuid:Boo'),RDF.value,Literal(2)))
    >>> token2 = ReteToken((URIRef('urn:uuid:Foo'),RDF.value,Literal(2)))
    >>> token3 = ReteToken((URIRef('urn:uuid:Foo'),RDF.type,URIRef('urn:uuid:Baz')),debug=True)
    >>> token4 = ReteToken((URIRef('urn:uuid:Bash'),RDF.type,URIRef('urn:uuid:Baz')))
    >>> token5 = ReteToken((URIRef('urn:uuid:Bar'),URIRef('urn:uuid:Prop1'),URIRef('urn:uuid:Beezle')),debug=True)
    >>> token6 = ReteToken((URIRef('urn:uuid:Bar'),URIRef('urn:uuid:Prop1'),URIRef('urn:uuid:Bundle')))
    >>> tokenList = [token1,token2,token3,token4,token5,token6]

    Setup the consequent (RHS) of the rule:
        { ?X rdf:value 1. ?X rdf:type ?Y. ?Z <urn:uuid:Prop1> ?W } => { ?X a <urn:uuid:SelectedVar> }
        
    a Network 'stub' is setup to capture the conflict set at the time the rule is fired
    
    >>> joinNode3.consequent.update([(Variable('X'),RDF.type,URIRef('urn:uuid:SelectedVar'))])
    >>> class NetworkStub:
    ...     def __init__(self):
    ...         self.firings = 0
    ...         self.conflictSet = Set()
    ...     def fireConsequent(self,tokens,termNode,debug):
    ...         self.firings += 1
    ...         self.conflictSet.add(tokens)
    >>> testHelper = NetworkStub()
    >>> joinNode3.network = testHelper

    Add the tokens sequentially to the top of the network (the alpha nodes).
    token3 triggers a trace through it's path down to the terminal node (joinNode2) 

    >>> aNode1.descendentMemory[0]
    <AlphaMemory: 0 item(s)>
    >>> aNode1.descendentMemory[0].position
    2
    >>> aNode1.activate(token1.unboundCopy())
    >>> aNode1.activate(token2.unboundCopy())
    >>> joinNode1.memories[LEFT_MEMORY]
    <BetaMemory: 0 item(s)>
    >>> joinNode2.memories[LEFT_MEMORY]
    <BetaMemory: 2 item(s)>
    >>> aNode1.activate(token3.unboundCopy())
    Propagated from <AlphaNode: (u'X', u'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', u'Y'). Feeds 1 beta nodes>
    (u'urn:uuid:Foo', u'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', u'urn:uuid:Baz')
    <BetaNode : CommonVariables: [u'X'] (2 in left, 1 in right memories)>.propagate(right,None,<ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>)
    activating with <PartialInstantiation (joined on ?X): Set([<ReteToken: X->urn:uuid:Foo>, <ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>])>
    
    Add the remaining 3 tokens (each fires the network)
    
    >>> aNode2.activate(token4.unboundCopy())
    >>> list(joinNode3.memories[LEFT_MEMORY])[0]
    <PartialInstantiation (joined on ?X): Set([<ReteToken: X->urn:uuid:Foo>, <ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>])>
    >>> aNode3.activate(token5.unboundCopy()))
    Propagated from <AlphaNode: (u'Z', u'urn:uuid:Prop1', u'W'). Feeds 1 beta nodes>
    (u'urn:uuid:Bar', u'urn:uuid:Prop1', u'urn:uuid:Beezle')
    <TerminalNode : CommonVariables: [] (1 in left, 1 in right memories)>.propagate(right,None,<ReteToken: Z->urn:uuid:Bar,W->urn:uuid:Beezle>)
    activating with <PartialInstantiation (joined on ?X): Set([<ReteToken: Z->urn:uuid:Bar,W->urn:uuid:Beezle>, <ReteToken: X->urn:uuid:Foo>, <ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>])>

    >>> aNode3.activate(token6.unboundCopy())
    >>> joinNode3
    <TerminalNode : CommonVariables: [] (1 in left, 2 in right memories)>
    >>> testHelper.firings
    2
    >>> pprint(testHelper.conflictSet)
    Set([<PartialInstantiation (joined on ?X): Set([<ReteToken: Z->urn:uuid:Bar,W->urn:uuid:Beezle>, <ReteToken: X->urn:uuid:Foo>, <ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>])>, <PartialInstantiation (joined on ?X): Set([<ReteToken: Z->urn:uuid:Bar,W->urn:uuid:Bundle>, <ReteToken: X->urn:uuid:Foo>, <ReteToken: X->urn:uuid:Foo,Y->urn:uuid:Baz>])>])
    """
    def __init__(self,
                 leftNode,
                 rightNode,
                 aPassThru=False,
                 leftVariables=None,
                 rightVariables=None,
                 executeActions=None,
                 ReteMemoryKind=ReteMemory):
        self.ReteMemoryKind = ReteMemoryKind
        self.instanciatingTokens = set()
        self.aPassThru = aPassThru 
        self.name = BNode()
        self.network = None
        
        #used by terminal nodes only
        self.consequent = set() #List of tuples in RHS
        self.rules = set()
        self.antecedent = None
        self.headAtoms = set()
        self.leftNode = leftNode
        self.rightNode = rightNode #The incoming right input of a BetaNode is always an AlphaNode
        self.memories = {}
        self.descendentMemory = []
        self.descendentBetaNodes = set()
        self.leftUnlinkedNodes = set()
        self.unlinkedMemory = None
        self.fedByBuiltin = None
        if isinstance(leftNode,BuiltInAlphaNode):
            self.fedByBuiltin = LEFT_MEMORY
            assert not isinstance(rightNode,BuiltInAlphaNode),"Both %s and %s are builtins feeding a beta node!"%(leftNode,rightNode)
            self.memories[RIGHT_MEMORY] = self.ReteMemoryKind((self,RIGHT_MEMORY,leftNode.n3builtin))
        else:
            self.memories[RIGHT_MEMORY] = self.ReteMemoryKind(self,RIGHT_MEMORY)
            
        assert not(self.fedByBuiltin),"No support for 'built-ins', function symbols, or non-equality tests"
        if isinstance(rightNode,BuiltInAlphaNode):
            self.fedByBuiltin = RIGHT_MEMORY
            assert not isinstance(leftNode,BuiltInAlphaNode),"Both %s and %s are builtins feeding a beta node!"%(leftNode,rightNode)
            self.memories[LEFT_MEMORY]  = self.ReteMemoryKind(self,LEFT_MEMORY,rightNode.n3builtin)
        else:
            self.memories[LEFT_MEMORY]  = self.ReteMemoryKind(self,LEFT_MEMORY)        
        if aPassThru:
            if rightNode:
                self.leftVariables = set() if leftVariables is None else leftVariables
                self.rightVariables = collectVariables(self.rightNode) if rightVariables is None else rightVariables
                self.commonVariables = list(self.rightVariables)
            else:
                self.leftVariables = self.rightVariables = set()
                self.commonVariables = []
        else: 
            self.leftVariables = collectVariables(self.leftNode) if leftVariables is None else leftVariables
            self.rightVariables = collectVariables(self.rightNode) if rightVariables is None else rightVariables        
            self.commonVariables = [leftVar for leftVar in self.leftVariables if leftVar in self.rightVariables]
        self.leftIndex  = {}
        self.rightIndex = {}
        self.executeActions = executeActions if executeActions is not None else {}

    def connectIncomingNodes(self,leftNode,rightNode):
        if leftNode:
            if self.leftNode and LEFT_UNLINKING:
                #candidate for left unlinking
                self.leftUnlinkedNodes.add(leftNode) 
                leftNode.unlinkedMemory = self.ReteMemoryKind(self,LEFT_MEMORY)
#                print "unlinked %s from %s"%(leftNode,self)
            elif self.leftNode:            
                leftNode.updateDescendentMemory(self.memories[LEFT_MEMORY])
                leftNode.descendentBetaNodes.add(self)        
        rightNode.updateDescendentMemory(self.memories[RIGHT_MEMORY])
        rightNode.descendentBetaNodes.add(self)
        
    def clauseRepresentation(self):
        if len(self.rules)>1:
            return "And(%s) :- %s"%(
                ' '.join([repr(atom) for atom in self.headAtoms]),
                self.antecedent
            )
        elif len(self.rules)>0:
            return repr(first(self.rules).formula)
        else:
            return ''
            
    def actionsForTerminalNode(self):
        for rhsTriple in self.consequent:
            override,executeFn = self.executeActions.get(rhsTriple,(None,None))
            if executeFn is not None:
                yield override, executeFn
        
    def __repr__(self):
        if self.executeActions:
            actionStr = ' with %s actions'%(len(list(self.actionsForTerminalNode())))
        else:
            actionStr = ''
        if self.consequent and self.fedByBuiltin:
            nodeType = 'TerminalBuiltin(%s)%s'%(
                self.memories[self._oppositeMemory(self.fedByBuiltin)].filter,actionStr)
        elif self.consequent:
            nodeType = 'TerminalNode%s (%s)'%(actionStr,self.clauseRepresentation())
        elif self.fedByBuiltin:
            nodeType = 'Builtin(%s)'%(self.memories[self._oppositeMemory(self.fedByBuiltin)].filter)
        else:            
            nodeType = 'BetaNode'
        if self.unlinkedMemory is not None:
            nodeType = 'LeftUnlinked-' + nodeType
        leftLen = self.memories[LEFT_MEMORY] and len(self.memories[LEFT_MEMORY]) or 0
        return "<%s %s: CommonVariables: %s (%s in left, %s in right memories)>"%(nodeType,self.aPassThru and "(pass-thru)" or '',self.commonVariables,leftLen,len(self.memories[RIGHT_MEMORY]))

    def _activate(self,partInstOrList,debug=False):
            if debug:
                print "activating with %s"%(partInstOrList)
            if self.unlinkedMemory is not None:
                if debug:
                    print "adding %s into unlinked memory"%(partInstOrList)                
                self.unlinkedMemory.addToken(partInstOrList,debug)                
            for memory in self.descendentMemory:  
                if debug:
                    print "\t## %s memory ##"%memoryPosition[memory.position]
                    print "\t",memory.successor
                    if memory.successor.consequent:
                        print "\t", memory.successor.clauseRepresentation()
                #print self,partInstOrList
                memory.addToken(partInstOrList,debug)
                if memory.successor.aPassThru or not memory.successor.checkNullActivation(memory.position):
                    if memory.position == LEFT_MEMORY:
                        memory.successor.propagate(memory.position,debug,partInstOrList)
                    else:
                        #print partInstOrList
                        memory.successor.propagate(None,debug,partInstOrList)
            
            if self.consequent:
                self.network.fireConsequent(partInstOrList,self,debug)

    def _unrollTokens(self,iterable):
        for token in iterable:
            if isinstance(token,PartialInstantiation):
                for i in token:
                    yield i
            else:
                yield token
                                             
    def _oppositeMemory(self,memoryPosition):
        if memoryPosition == LEFT_MEMORY:
            return RIGHT_MEMORY
        else:
            return LEFT_MEMORY
            
    def _checkOpposingMemory(self,memoryPosition):
        return bool(len(self.memories[self._oppositeMemory(memoryPosition)]))

    def checkNullActivation(self,source):
        """
        Checks whether this beta node is involved in a NULL activation relative to the source.
        NULL activations are where one of the opposing memories that feed
        this beta node are empty.  Takes into account built-in filters/function.
        source is the position of the 'triggering' memory (i.e., the memory that had a token added)
        """        
        oppositeMem = self.memories[self._oppositeMemory(source)]
        return not self.fedByBuiltin and not oppositeMem
            
    def propagate(self,propagationSource,debug = False,partialInst=None,wme=None):
        """
        .. 'activation' of Beta Node - checks for consistent 
        variable bindings between memory of incoming nodes ..
        Beta (join nodes) with no variables in common with both ancestors
        activate automatically upon getting a propagation 'signal'

        """
        if debug and propagationSource:
            print "%s.propagate(%s,%s,%s)"%(self,memoryPosition[propagationSource],partialInst,wme)
            print "### Left Memory ###"
            pprint(list(self.memories[LEFT_MEMORY]))
            print "###################"
            print "### Right Memory ###"
            pprint(list(self.memories[RIGHT_MEMORY]))
            print "####################"
            print self.clauseRepresentation()
        if self.aPassThru:
            if self.consequent:
                if self.rightNode is None:
                    assert partialInst is not None
                    self._activate(partialInst,debug)                
                else:
                    assert not partialInst,"%s,%s"%(partialInst,wme)
                    self._activate(PartialInstantiation([wme],consistentBindings=wme.bindingDict.copy()),debug)                
                
            elif self.memories[RIGHT_MEMORY]:
                #pass on wme as an unjoined partInst
                #print self
                if wme:
                    self._activate(PartialInstantiation([wme],consistentBindings=wme.bindingDict.copy()),debug)
                elif partialInst:
                    #print "## Problem ###"
                    #print "%s.propagate(%s,%s,%s)"%(self,memoryPosition[propagationSource],partialInst,wme)
                    self._activate(partialInst,debug)                
        elif not propagationSource:
            #Beta node right activated by another beta node
            #Need to unify on common variable hash, using the bindings
            #provided by the partial instantiation that triggered the activation
            if partialInst:
                for binding in partialInst.bindings:
                    # for var in self.commonVariables:
                        # if var not in binding:
                        #     import pdb;pdb.set_trace()
                    try:
                        commonVals = tuple([binding[var] for var in self.commonVariables])
                        lTokens = self.memories[RIGHT_MEMORY].substitutionDict.get(commonVals,set())
                        rTokens = self.memories[LEFT_MEMORY].substitutionDict.get(commonVals,set())
                        joinedTokens = set(self._unrollTokens(rTokens | lTokens))
                        if joinedTokens:                    
                            commonDict = dict([(var,list(commonVals)[self.commonVariables.index(var)]) for var in self.commonVariables])
                            newP = PartialInstantiation(joinedTokens,consistentBindings=commonDict)
                            self._activate(newP,debug)            
                    except KeyError:
                        print "\tProblem with ", partialInst
            
        elif propagationSource == LEFT_MEMORY:
            #Doesn't check for null left activation! - cost is mitigated by 
            #left activation, partialInst passed down
            #procedure join-node-left-activation (node: join-node, t: token)
            #     for each w in node.amem.items do
            #         if perform-join-tests (node.tests, t, w) then
            #             for each child in node.children do left-activation (child, t, w)
            # end            
            matches = set()
            if self.fedByBuiltin:
                builtin = self.memories[self._oppositeMemory(self.fedByBuiltin)].filter
                newConsistentBindings = [term for term in [builtin.argument,
                                                           builtin.result] 
                                                if isinstance(term,Variable) and \
                                                term not in partialInst.joinedBindings]
                partialInst.addConsistentBinding(newConsistentBindings)
                for binding in partialInst.bindings:
                    lhs = builtin.argument
                    rhs = builtin.result
                    lhs = binding.get(lhs) if isinstance(lhs,Variable) else lhs
                    rhs = binding.get(rhs) if isinstance(rhs,Variable) else rhs
                    assert lhs is not None and rhs is not None
                    if builtin.func(lhs,rhs):
                        if debug:
                            print "\t%s + %s => True"%(binding,builtin)
                        matches.add(partialInst)
                    else:
                        if debug:
                            print "\t%s + %s => False"%(binding,builtin)
            else:
                for binding in partialInst.bindings:
                    #iterate over the binding combinations 
                    #and use the substitutionDict in the right memory to find matching WME'a
                    if debug:
                        print "\t", binding
                        
                    substitutedTerm=[]
                    commonDictKV=[]
                    for var in self.commonVariables:
                        if var not in binding:
                            continue
                        else:
                            commonDictKV.append((var,binding[var]))
                            substitutedTerm.append(binding[var])
                    rWMEs = self.memories[RIGHT_MEMORY].substitutionDict.get(tuple(substitutedTerm),
                                                                             set())
                    commonDict = dict(commonDictKV)
                    if debug:
                        print commonDict,rWMEs, self.memories[RIGHT_MEMORY].substitutionDict.keys()
                    for rightWME in rWMEs:
                        if isinstance(rightWME,ReteToken):
                            matches.add(partialInst.newJoin(
                                rightWME,
                                ifilter(lambda x:x not in partialInst.joinedBindings,
                                    self.commonVariables)))
                            # [var for var in self.commonVariables if var not in partialInst.joinedBindings]))
                        else:
                            #Joining two Beta/Join nodes!
                            joinedTokens = list(partialInst.tokens | rightWME.tokens)
                            #print "### joining two tokens ###"
                            #pprint(joinedTokens)
                            if self.consequent:
                                for consequent in self.consequent:
                                    consVars = ifilter(lambda x:isinstance(x,Variable),consequent)
                                    # [i for i in consequent if isinstance(i,Variable)]                                
                                failed = True
                                for binding in PartialInstantiation(joinedTokens,consistentBindings=commonDict).bindings:
                                    if any(consVars,lambda x:x not in binding):# [key for key in consVars if key not in binding]:
                                        continue
                                    else:
                                        failed = False                                                                    
                                if not failed:                                        
                                    newP = PartialInstantiation(joinedTokens,consistentBindings=commonDict)
                                    matches.add(newP)
                            else:
                                newP = PartialInstantiation(joinedTokens,consistentBindings=commonDict)
                                matches.add(newP)
                                
            for pInst in matches:
                self._activate(pInst,debug)                    
        else:            
            #right activation, partialInst & wme passed down
            #procedure join-node-right-activation (node: join-node, w: WME)
            #    for each t in node.parent.items do {"parent" is the beta memory node}
            #        if perform-join-tests (node.tests, t, w) then
            #            for each child in node.children do left-activation (child, t, w)
            #end
            #pprint(self.memories[self._oppositeMemory(propagationSource)])
            matches = set()
            try:
                lPartInsts = self.memories[LEFT_MEMORY].substitutionDict.get(tuple([wme.bindingDict[var] for var in self.commonVariables]))
            except:
                raise Exception("%s and %s"%(repr(self),repr(wme.bindingDict)))
            if lPartInsts:
                for partialInst in lPartInsts:
                    if not isinstance(partialInst,PartialInstantiation):
                        singleToken = PartialInstantiation([partialInst],consistentBindings=partialInst.bindingDict.copy())
                        matches.add(singleToken)
                    else:
                        assert isinstance(partialInst,PartialInstantiation),repr(partialInst)
                        matches.add(partialInst.newJoin(
                                        wme,
                                        ifilter(lambda x:x not in partialInst.joinedBindings,
                                                self.commonVariables)))
                                    # [var for var in self.commonVariables if var not in partialInst.joinedBindings]))
            for pInst in matches:
                self._activate(pInst,debug)  

TEST_NS = Namespace('http://example.com/text1/')

def PopulateTokenFromANode(aNode,bindings):
    #print aNode, bindings
    termList = [isinstance(term,Variable) and bindings[term] or term
                    for term in aNode.triplePattern]
    token = ReteToken(tuple(termList))
    token.bindVariables(aNode)
    return token

class PartialInstantiationTests(unittest.TestCase):
    def testConsistentBinding(self):
        allBindings = {}
        allBindings.update(self.joinedBindings)
        allBindings.update(self.unJoinedBindings)
        aNodes = [self.aNode1,
                  self.aNode2,
                  self.aNode5,
                  self.aNode6,
                  self.aNode7,
                  self.aNode8,
                  self.aNode9,
                  self.aNode10,
                  self.aNode11]
        pToken = PartialInstantiation(
                      tokens = [PopulateTokenFromANode(aNode,
                                                       allBindings) 
                                  for aNode in aNodes],
                      consistentBindings = self.joinedBindings)
        #print pToken
        pToken.addConsistentBinding(self.unJoinedBindings.keys())
        #print pToken.joinedBindings
        for binding in pToken.bindings:
            for key in self.unJoinedBindings:
                self.failUnless(key in binding, "Missing key %s from %s"%(key,binding))
                        
    def setUp(self):
        self.aNode1 = AlphaNode((Variable('HOSP'),
                                 TEST_NS.contains,
                                 Variable('HOSP_START_DATE')))                
        self.aNode2 = AlphaNode((Variable('HOSP'),
                                 RDF.type,
                                 TEST_NS.Hospitalization))                
        self.aNode5 = AlphaNode((Variable('HOSP_START_DATE'),
                                 TEST_NS.dateTimeMin,
                                 Variable('ENCOUNTER_START')))                
        self.aNode6 = AlphaNode((Variable('HOSP_STOP_DATE'),
                                 RDF.type,
                                 TEST_NS.EventStopDate))                
        self.aNode7 = AlphaNode((Variable('HOSP_STOP_DATE'),
                                 TEST_NS.dateTimeMax,
                                 Variable('ENCOUNTER_STOP')))                
        self.aNode8 = AlphaNode((Variable('EVT_DATE'),
                                 RDF.type,
                                 TEST_NS.EventStartDate))                
        self.aNode9 = AlphaNode((Variable('EVT_DATE'),
                                 TEST_NS.dateTimeMin,
                                 Variable('EVT_START_MIN')))                
        self.aNode10 =AlphaNode((Variable('EVT'),
                                 TEST_NS.contains,
                                 Variable('EVT_DATE')))                
        self.aNode11 =AlphaNode((Variable('EVT'),
                                 RDF.type,
                                 Variable('EVT_KIND')))

        self.joinedBindings = {Variable('HOSP_START_DATE'):
                               BNode(),
                               Variable('HOSP_STOP_DATE'):
                               BNode(),
                               Variable('HOSP'):
                               BNode()}
        self.unJoinedBindings = {Variable('EVT'):
                                 BNode(),
                                 Variable('EVT_DATE'):
                                 BNode(),
                                 Variable('EVT_KIND'):
                                 TEST_NS.ICUStay}
        for dtVariable in [Variable('ENCOUNTER_START'),
                           Variable('ENCOUNTER_STOP'),
                           Variable('EVT_START_MIN')]:
            self.unJoinedBindings[dtVariable]=Literal("2007-02-14T10:00:00",
                                                      datatype=_XSD_NS.dateTime)
                                  
def test():
#    import doctest
#    doctest.testmod()
    suite = unittest.makeSuite(PartialInstantiationTests)
    unittest.TextTestRunner(verbosity=5).run(suite)    

if __name__ == '__main__':
    test()
