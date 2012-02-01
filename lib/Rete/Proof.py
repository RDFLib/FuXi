#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
Proof Markup Language Construction: Proof Level Concepts (Abstract Syntax)

A set of Python objects which create a PML instance in order to serialize as OWL/RDF

"""
try:    
    import boost.graph as bgl
    bglGraph = bgl.Digraph()
except:
    try:
        from pydot import Node,Edge,Dot
        dot=Dot(graph_type='digraph')
    except:
        import warnings
        warnings.warn("Missing pydot library",ImportWarning)                
#        raise NotImplementedError("Boost Graph Library & Python bindings (or pydot) not installed.  See: see: http://www.osl.iu.edu/~dgregor/bgl-python/")

from itertools import izip,ifilter,ifilterfalse
from FuXi.Syntax.InfixOWL import *
from FuXi.Horn.HornRules import Clause, Ruleset
from FuXi.Horn.PositiveConditions import Uniterm, buildUniTerm, SetOperator, Exists
from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstantiation, project
from FuXi.Rete.RuleStore import N3Builtin
from FuXi.Rete.AlphaNode import AlphaNode, ReteToken
from FuXi.Rete.Network import _mulPatternWithSubstitutions
try:
    from rdflib.graph import Graph
    from rdflib.namespace import NamespaceManager
except ImportError:
    from rdflib.Graph import Graph
    from rdflib.syntax.NamespaceManager import NamespaceManager
from rdflib import Namespace, BNode, Variable
from pprint import pprint,pformat

#From itertools recipes
def iteritems(mapping): 
    return izip(mapping.iterkeys(),mapping.itervalues())

def any(seq,pred=None):
    """Returns True if pred(x) is true for at least one element in the iterable"""
    for elem in ifilter(pred,seq):
        return True
    return False

def all(seq, pred=None):
    "Returns True if pred(x) is true for every element in the iterable"
    for elem in ifilterfalse(pred, seq):
        return False
    return True

def fillBindings(terms,bindings):
    for term in terms:
        if isinstance(term,Variable):
            yield bindings[term]
        else:
            yield term 
def termIterator(term):
    if isinstance(term,(Exists,SetOperator)):
        for i in term:
            yield i
    else:
        yield term
        
class ImmutableDict(dict):
    '''
    A hashable dict.
    
    >>> a=[ImmutableDict([('one',1),('three',3)]),ImmutableDict([('two',2),('four' ,4)])]
    >>> b=[ImmutableDict([('two',2),('four' ,4)]),ImmutableDict([('one',1),('three',3)])]
    >>> a.sort(key=lambda d:hash(d))
    >>> b.sort(key=lambda d:hash(d))
    >>> a == b
    True
    
    '''
    def __init__(self,*args,**kwds):
        dict.__init__(self,*args,**kwds)
        self._items=list(self.iteritems())
        self._items.sort()
        self._items=tuple(self._items)
    def __setitem__(self,key,value):
        raise NotImplementedError, "dict is immutable"
    def __delitem__(self,key):
        raise NotImplementedError, "dict is immutable"
    def clear(self):
        raise NotImplementedError, "dict is immutable"
    def setdefault(self,k,default=None):
        raise NotImplementedError, "dict is immutable"
    def popitem(self):
        raise NotImplementedError, "dict is immutable"
    def update(self,other):
        raise NotImplementedError, "dict is immutable"
    def normalize(self):
        return dict([(k,v) for k,v in self.items()])
    def __hash__(self):
        return hash(self._items)
    
def MakeImmutableDict(regularDict):
    """
    Takes a regular dicitonary and makes an immutable dictionary out of it
    """
    return ImmutableDict([(k,v) 
                           for k,v in regularDict.items()])
                    
def fetchRETEJustifications(goal,nodeset,builder,antecedent=None):
    """
    Takes a goal, a nodeset and an inference step the nodeset is the
    premise for the corresponding rule.  Returns a generator
    over the valid terminal nodes that are responsible for inferring
    the conclusion represented by the nodeset
    """
    #The justification indicated by the RETE network
    justificationForGoal =  nodeset.network.justifications[goal]
    if antecedent:
        yielded = False
        #might not be a valid justification
        for reteJustification in justificationForGoal:
            validJustification = True
            for bodyTerm in reteJustification.clause.body:
                #is the premise already proven?
                failedCheck = True
                try:
                    failedCheck = any(termIterator(bodyTerm),lambda x:
                                          tuple(fillBindings(x.toRDFTuple(),antecedent.bindings))
                                             in builder.goals)
                except KeyError:
                    failedCheck = False
                validJustification = not failedCheck
            if validJustification:
                yielded = True
                yield reteJustification
        if not yielded:
            for tNode in nodeset.network.terminalNodes:
                if tNode not in justificationForGoal:
                    try:
                        if any(termIterator(tNode.clause.head),
                               lambda x:
                                  tuple(fillBindings(x.toRDFTuple(),
                                                     antecedent.bindings)) == goal):
                            yield tNode 
                    except Exception,e:
                        pass
    else:
        for tNode in justificationForGoal:
            yield tNode

PML = Namespace('http://inferenceweb.stanford.edu/2004/07/iw.owl#')
PML_P = Namespace('http://inferenceweb.stanford.edu/2006/06/pml-provenance.owl#')
FUXI=URIRef('http://purl.org/net/chimezie/FuXi')
GMP_NS = Namespace('http://inferenceweb.stanford.edu/registry/DPR/GMP.owl#')

def GenerateProof(network,goal):
    builder=ProofBuilder(network)
    proof=builder.buildNodeSet(goal,proof=True)
    assert goal in network.inferredFacts
    return builder,proof

class ProofBuilder(object):
    """
    Handles the recursive building of a proof tree (from a 'fired' RETE-UL network), 
    keeping the state of the goals already processed

    We begin by defining a proof as a sequence of ‚proof steps, where each
    proof step consists of a conclusion, a justification for that conclusion, and a set
    of assumptions discharged by the step. ‚A proof of C‚ is defined to be a proof
    whose last step has conclusion C. A proof of C is conditional on an assumption
    A if and only if there is a step in the proof that has A as its conclusion and
    ‚assumption‚ as its justification, and A is not discharged by a later step in the
    proof.    
    
    """
    def __init__(self,network):
        self.goals = {}
        self.network = network
        self.trace=[]
        self.serializedNodeSets = set()
        
    def extractGoalsFromNode(self, node):
        """
        Start with given node and inductively extract the relevant
        nodesets into the builder
        """
        if isinstance(node,NodeSet):
            if node.conclusion not in self.goals:
                self.goals[node.conclusion] = node
                for step in node.steps:
                    self.extractGoalsFromNode(step)
        else:
            self.extractGoalsFromNode(node.parent)
            for ant in node.antecedents:
                self.extractGoalsFromNode(ant)

    def serialize(self,proof,proofGraph):
        proof.serialize(self,proofGraph)
        
    def renderProof(self,proof,nsMap = {}):
        """
        Takes an instance of a compiled ProofTree and a namespace mapping (for constructing QNames
        for rule pattern terms) and returns a BGL Digraph instance representing the Proof Tree
        """
        try:    
            import boost.graph as bgl
            bglGraph = bgl.Digraph()
        except:
            try:
                from pydot import Node,Edge,Dot
                dot=Dot(graph_type='digraph')
            except:
                raise NotImplementedError("No graph libraries")
        # namespace_manager = NamespaceManager(Graph())
        # vertexMaps   = {}
        # edgeMaps     = {}
#        for prefix,uri in nsMap.items():
#            namespace_manager.bind(prefix, uri, override=False)
        visitedNodes = {}
        # edges = []
        idx = 0
        #register the step nodes
        for nodeset in self.goals.values():
            if not nodeset in visitedNodes:
                idx += 1
                visitedNodes[nodeset] = nodeset.generateGraphNode(str(idx),nodeset is proof)
            #register the justification steps
            for justification in nodeset.steps:
                if not justification in visitedNodes:
                    idx += 1
                    visitedNodes[justification] = justification.generateGraphNode(str(idx))
                    for ant in justification.antecedents:
                        if ant not in visitedNodes:
                            idx += 1
                            visitedNodes[ant] = ant.generateGraphNode(str(idx))
        for node in visitedNodes.values():
            dot.add_node(node)
        for nodeset in self.goals.values():
            for justification in nodeset.steps:
                edge = Edge(visitedNodes[nodeset],
                            visitedNodes[justification],
                            label="is the consequence of",
                            color = 'red')
                dot.add_edge(edge)
                                
                for ant in justification.antecedents:
                    if justification.source:
                        edge = Edge(visitedNodes[ant.steps[0]],
                                    visitedNodes[nodeset],
                                    label="has antecedent",
                                    color='blue')                        
                        dot.add_edge(edge)
                    else:#not isinstance(justification,InferenceStep) or not justification.source:#(visitedNodes[nodeset],visitedNodes[justification]) not in edges:
                        edge = Edge(visitedNodes[justification],
                                    visitedNodes[ant],
                                    label="has antecedent",
                                    color='blue')
                        #edge.label="has antecedents"
                        dot.add_edge(edge)
                        #edges.append((visitedNodes[nodeset],visitedNodes[justification]))
                                                                
        return dot#bglGraph
                
    def buildInferenceStep(self,parent,terminalNode,goal):
        """
        Takes a Node set and builds an inference step which contributes to its
        justification, recursively marking its ancestors (other dependent node sets / proof steps).
        So this recursive method builds a proof tree 'upwards' from the original goal
        
        This iterates over the tokens which caused the terminal node to 'fire'
        and 'prooves' them by first checking if they are inferred or if they were asserted.
        """
        #iterate over the tokens which caused the instantiation of this terminalNode
        step = InferenceStep(parent,terminalNode.clause)
        bindings={}
        for _dict in self.network.proofTracers[goal]:
            bindings.update(_dict)
        step.bindings.update(bindings)      
        if ReteToken(goal) in self.network.workingMemory:
            step.source='some RDF graph'
            self.trace.append("Marking justification from assertion for "+repr(goal))
        for tNode in fetchRETEJustifications(goal,parent,self,step):
            if self.network.instantiations[tNode]:
                for bodyTerm in tNode.clause.body:
                    step.rule = tNode.clause
                    for termVar in termIterator(bodyTerm):       
                        assert isinstance(termVar,(Uniterm,N3Builtin))
                        a=[x for x in termVar.toRDFTuple() if isinstance(x,Variable) and x not in step.bindings]
                    binds=[]
                    for t in tNode.instanciatingTokens:
                        binds.extend([project(binding,a) for binding in t.bindings])
                    binds=set([ImmutableDict([(k,v) for k,v in bind.items()]) for bind in binds])
                    assert len(binds)<2
                    for b in binds:
                        step.bindings.update(b)
                    for termVar in termIterator(bodyTerm):       
                        assert isinstance(termVar,(N3Builtin,Uniterm))
                        assert all(termVar.toRDFTuple(), 
                                   lambda x:isinstance(x,Variable) and x in step.bindings or not isinstance(x, Variable))      
                    groundAntecedentAssertion = tuple(fillBindings(bodyTerm.toRDFTuple(), step.bindings))
                    self.trace.append("Building inference step for %s"%parent)
                    self.trace.append("Inferred from RETE node via %s"%(tNode.clause))
                    self.trace.append("Bindings: %s"%step.bindings)
                    step.antecedents.append(self.buildNodeSet(groundAntecedentAssertion,antecedent=step))                    
        return step
        
    def buildNodeSet(self,goal,antecedent=None,proof=False):
        if not goal in self.network.justifications:
            #Not inferred, must have been originally asserted
            #assert goal not in self.network.workingMemory
            self.trace.append("Building %s around%sgoal (justified by a direct assertion): %s"%(proof and 'proof' or 'nodeset',
                                                                                              antecedent and ' antecedent ' or '',str(buildUniTerm(goal,self.network.nsMap))))
            # assertedSteps = [token.asTuple() for token in self.network.workingMemory]
            #assert goal in assertedSteps
            if goal in self.goals:
                ns=self.goals[goal]
                self.trace.append("Retrieving prior nodeset %s for %s"%(ns,goal))
            else:
                idx=BNode()
                ns=NodeSet(goal,network=self.network,identifier=idx)
                self.goals[goal]=ns
                ns.steps.append(InferenceStep(ns,source='some RDF graph'))
                self.trace.append("Marking justification from assertion for "+repr(goal))
        else:
            if goal in self.goals:
                ns=self.goals[goal]
                self.trace.append("Retrieving prior nodeset %s for %s"%(ns,goal))
            else:
                self.trace.append("Building %s around%sgoal: %s"%(proof and 'proof' or 'nodeset',
                                                                antecedent and ' antecedent ' or ' ',str(buildUniTerm(goal,self.network.nsMap))))                
                idx=BNode()
                ns=NodeSet(goal,network=self.network,identifier=idx)
                self.goals[goal]=ns
                ns.steps = [self.buildInferenceStep(ns,tNode,goal) 
                                for tNode in fetchRETEJustifications(goal,ns,self)]
                assert ns.steps
        return ns

class NodeSet(object):
    """
    represents a step in a proof whose conclusion is justified by any
    of a set of inference steps associated with the NodeSet. 
    
    The Conclusion of a node set represents the expression concluded by the
    proof step. Every node set has one conclusion, and a conclusion of a node
    set is of type Expression.
    
    Each inference step of a node set represents an application of an inference
    rule that justifies the node set's conclusion. A node set can have any
    number of inference steps, including none, and each inference step of a
    node set is of type InferenceStep. A node set without inference steps is of a special kind identifying an
    unproven goal in a reasoning process as described in Section 4.1.2 below.
    
    """
    def __init__(self,conclusion=None,steps=None,identifier=BNode(),network=None, naf =False):
        if network:
            self.network=network
        else:
            self.network = self
            self.network.nsMap = {}
        self.identifier = identifier
        self.conclusion = conclusion
        self.language = None
        self.naf = naf
        self.steps = steps and steps or []

    def serialize(self,builder,proofGraph):
        conclusionPrefix=self.naf and 'not ' or ''
        proofGraph.add((self.identifier,
                        PML.hasConclusion,
                        Literal("%s%s"%(conclusionPrefix,
                                        repr(buildUniTerm(self.conclusion,
                                                  self.network.nsMap))))))
        #proofGraph.add((self.identifier,PML.hasLanguage,URIRef('http://inferenceweb.stanford.edu/registry/LG/RIF.owl')))
        proofGraph.add((self.identifier,RDF.type,PML.NodeSet))
        for step in self.steps:
            proofGraph.add((self.identifier,PML.isConsequentOf,step.identifier))
            builder.serializedNodeSets.add(self.identifier)
            step.serialize(builder,proofGraph)

    def generateGraphNode(self,idx,proofRoot=False):
        vertex = Node(idx,label='"%s"'%repr(self),shape='plaintext')
#        vertex.shape = 'plaintext'
#        vertex.width = '5em'
        if proofRoot:
            vertex.root = 'true'
#        vertex.peripheries = '1'
        return vertex
    
    def __repr__(self):
        #rt="Proof step for %s with %s justifications"%(buildUniTerm(self.conclusion),len(self.steps))
        conclusionPrefix=self.naf and 'not ' or ''
        rt="Proof step for %s%s"%(conclusionPrefix,
                                  buildUniTerm(self.conclusion,self.network and self.network.nsMap or {}))
        return rt
    
class InferenceStep(object):
    """
    represents a justification for the conclusion of a node set.
    
    The rule of an inference step, which is the value of the property hasRule of
    the inference step, is the rule that was applied to produce the conclusion.
    Every inference step has one rule, and that rule is of type InferenceRule
    (see Section 3.3.3). Rules are in general registered in the IWBase by engine
    developers. However, PML specifies three special instances of rules:
    Assumption, DirectAssertion, and UnregisteredRule.    

    The antecedents of an inference step is a sequence of node sets each of
    whose conclusions is a premise of the application of the inference step's
    rule. The sequence can contain any number of node sets including none.
    The sequence is the value of the property hasAntecedent of the inference
    step.
    
    Each binding of an inference step is a mapping from a variable to a term
    specifying the substitutions performed on the premises before the application
    of the step's rule. For instance, substitutions may be required to
    unify terms in premises in order to perform resolution. An inference step
    can have any number of bindings including none, and each binding is of
    type VariableBinding. The bindings are members of a collection that is the
    value of the property hasVariableMapping of the inference step.    

    Each discharged assumption of an inference step is an expression that is
    discharged as an assumption by application of the step's rule. An inference
    step can have any number of discharged assumptions including none,
    and each discharged assumption is of type Expression. The discharged assumptions
    are members of a collection that is the value of the property
    hasDischargeAssumption of the inference step. This property supports
    the application of rules requiring the discharging of assumptions such as
    natural deduction's implication introduction. An assumption that is discharged
    at an inference step can be used as an assumption in the proof
    of an antecedent of the inference step without making the proof be conditional
    on that assumption.
    
    """
    def __init__(self,parent,rule=None,bindings=None,source=None):
        self.identifier=BNode()
        self.source = source
        self.parent = parent
        self.bindings = bindings and bindings or {}
        self.rule = rule
        self.antecedents = []
        self.groundQuery = None

    def propagateBindings(self,bindings):
        self.bindings.update(bindings)

    def serialize(self,builder,proofGraph):
        if self.rule and not self.source:
            proofGraph.add((self.identifier,PML.englishDescription,Literal(repr(self))))
        if self.groundQuery and (self.identifier,None,None) not in proofGraph:
            query= BNode()
            info = BNode()
            proofGraph.add((self.identifier,PML.fromQuery,query))
            proofGraph.add((query,RDF.type,PML.Query))
            proofGraph.add((query,PML_P.hasContent,info))
            proofGraph.add((info,RDF.type,PML_P.Information))
            proofGraph.add((info,PML_P.hasRawString,Literal(self.groundQuery)))
        elif self.source:
            someDoc = BNode()
            proofGraph.add((self.identifier,PML_P.hasSource,someDoc))
            proofGraph.add((someDoc,RDF.type,PML_P.Document))
            
            
        #proofGraph.add((self.identifier,PML.hasLanguage,URIRef('http://inferenceweb.stanford.edu/registry/LG/RIF.owl')))
        proofGraph.add((self.identifier,RDF.type,PML.InferenceStep))
        proofGraph.add((self.identifier,PML.hasInferenceEngine,FUXI))
        proofGraph.add((self.identifier,PML.hasRule,GMP_NS.GMP))
        proofGraph.add((self.identifier,PML.consequent,self.parent.identifier))
        for ant in self.antecedents:
            proofGraph.add((self.identifier,PML.hasAntecedent,ant.identifier))
            ant.serialize(builder,proofGraph)
        for k,v in self.bindings.items():
            mapping=BNode()
            proofGraph.add((self.identifier,PML.hasVariableMapping,mapping))
            proofGraph.add((mapping,RDF.type,PML.Mapping))
            proofGraph.add((mapping,PML.mapFrom,k))
            proofGraph.add((mapping,PML.mapTo,v))

    def generateGraphNode(self,idx):
        vertex = Node(idx,label='"%s"'%repr(self),shape='box')
        vertex.shape = 'plaintext'
        return vertex
        #shapeMap[vertex] = 'box'
        #sizeMap[vertex] = '10'
        #outlineMap[vertex] = '1'
    def iterCondition(self,condition):
        return isinstance(condition,SetOperator) and condition or iter([condition])

    def prettyPrintRule(self):
        if len(list(self.iterCondition(self.rule.body)))  > 2:
            return "And(%s)"%repr(self.rule.head)+':-'+'\\n\\t'.join([repr(i) for i in self.rule.body]) 
        return repr(self.rule)

    def __repr__(self):
        from FuXi.Rete.Magic import AdornedUniTerm
        if self.groundQuery:
            return self.groundQuery
        elif self.source:
            return "[Parsing RDF source]"
        elif self.rule:
            if isinstance(self.rule.head,AdornedUniTerm) and self.rule.head.isMagic:
                return "magic predicate justification\\n%s"%(self.rule)
            else:
                return repr(self.rule)#self.prettyPrintRule()
