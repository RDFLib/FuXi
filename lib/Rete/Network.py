"""
A Rete Network Building and 'Evaluation' Implementation for RDFLib Graphs of Notation 3 rules.
The DLP implementation uses this network to automatically building RETE decision trees for OWL forms of
DLP

Uses Python hashing mechanism to maximize the efficiency of the built pattern network.

The network :
    - compiles an RDFLib N3 rule graph into AlphaNode and BetaNode instances
    - takes a fact (or the removal of a fact, perhaps?) and propagates down, starting from it's alpha nodes
    - stores inferred triples in provided triple source (an RDFLib graph) or a temporary IOMemory Graph by default

"""
from itertools import izip,ifilter,chain
import time,sys
from pprint import pprint
from cStringIO import StringIO
from Util import xcombine
from BetaNode import BetaNode, LEFT_MEMORY, RIGHT_MEMORY, PartialInstanciation
from AlphaNode import AlphaNode, ReteToken, SUBJECT, PREDICATE, OBJECT, BuiltInAlphaNode
from BuiltinPredicates import FILTERS
from FuXi.Horn import ComplementExpansion, DATALOG_SAFETY_NONE, \
                      DATALOG_SAFETY_STRICT, DATALOG_SAFETY_LOOSE
from FuXi.Syntax.InfixOWL import *
from FuXi.Horn.PositiveConditions import Uniterm, SetOperator, Exists, Or
from FuXi.DLP import MapDLPtoNetwork,non_DHL_OWL_Semantics,IsaFactFormingConclusion
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from Util import generateTokenSet,renderNetwork
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS
from rdflib.util import first
from rdflib.Collection import Collection
from rdflib.Graph import ConjunctiveGraph,QuotedGraph,ReadOnlyGraphAggregate, Graph
from rdflib.syntax.NamespaceManager import NamespaceManager
from ReteVocabulary import RETE_NS
from RuleStore import N3RuleStore,N3Builtin, Formula
OWL_NS    = Namespace("http://www.w3.org/2002/07/owl#")
Any = None
LOG = Namespace("http://www.w3.org/2000/10/swap/log#")

#From itertools recipes
def iteritems(mapping): 
    return izip(mapping.iterkeys(),mapping.itervalues())

def any(seq,pred=None):
    """Returns True if pred(x) is true for at least one element in the iterable"""
    for elem in ifilter(pred,seq):
        return True
    return False

class HashablePatternList(object):
    """
    A hashable list of N3 statements which are patterns of a rule.  Order is disregarded
    by sorting based on unicode value of the concatenation of the term strings 
    (in both triples and function builtins invokations).  
    This value is also used for the hash.  In this way, patterns with the same terms
    but in different order are considered equivalent and share the same Rete nodes
    
    >>> nodes = {}
    >>> a = HashablePatternList([(Variable('X'),Literal(1),Literal(2))])
    >>> nodes[a] = 1
    >>> nodes[HashablePatternList([None]) + a] = 2
    >>> b = HashablePatternList([(Variable('Y'),Literal(1),Literal(2))])
    >>> b in a
    True
    >>> a == b 
    True
     
    """
    def __init__(self,items=None,skipBNodes=False):
        self.skipBNodes = skipBNodes
        if items:
            self._l = items
        else:
            self._l = []
            
    def _hashRulePattern(self,item):
        """
        Generates a unique hash for RDF triples and N3 builtin invokations.  The
        hash function consists of the hash of the terms concatenated in order
        """
        if isinstance(item,tuple):
            return reduce(lambda x,y:x+y,[ i for i in item 
                                            if not self.skipBNodes or not isinstance(i,BNode)])
        elif isinstance(item,N3Builtin):
            return reduce(lambda x,y:x+y,[item.argument,item.result])
            
    def __len__(self):
        return len(self._l)
    
    def __getslice__(self,beginIdx,endIdx):        
        return HashablePatternList(self._l[beginIdx:endIdx])
    
    def __hash__(self):
        if self._l:
            _concatPattern = [pattern and self._hashRulePattern(pattern) or "None" for pattern in self._l]
            #nulify the impact of order in patterns
            _concatPattern.sort()
            return hash(reduce(lambda x,y:x+y,_concatPattern))
        else:
            return hash(None)
    def __add__(self,other):
        assert isinstance(other,HashablePatternList),other
        return HashablePatternList(self._l + other._l)
    def __repr__(self):
        return repr(self._l)
    def extend(self,other):
        assert isinstance(other,HashablePatternList),other
        self._l.extend(other._l)
    def append(self,other):
        self._l.append(other)
    def __iter__(self):
        return iter(self._l)
    def __eq__(self,other):
        return hash(self) == hash(other)   

def _mulPatternWithSubstitutions(tokens,consequent,termNode):
    """
    Takes a set of tokens and a pattern and returns an iterator over consequent 
    triples, created by applying all the variable substitutions in the given tokens against the pattern
    
    >>> aNode = AlphaNode((Variable('S'),Variable('P'),Variable('O')))
    >>> token1 = ReteToken((URIRef('urn:uuid:alpha'),OWL_NS.differentFrom,URIRef('urn:uuid:beta')))
    >>> token2 = ReteToken((URIRef('urn:uuid:beta'),OWL_NS.differentFrom,URIRef('urn:uuid:alpha')))
    >>> token1 = token1.bindVariables(aNode)
    >>> token2 = token2.bindVariables(aNode)
    >>> inst = PartialInstanciation([token1,token2])
    """
    success = False
    for binding in tokens.bindings:        
        tripleVals = []
        # if any(consequent,
        #        lambda term:isinstance(term,Variable) and term not in binding):#  not mismatchedTerms:
        #     return
        # else:
        for term in consequent:
            if isinstance(term,(Variable,BNode)) and term in binding:
                #try:                
                tripleVals.append(binding[term])
                #except:
                #    pass
            else:                    
                tripleVals.append(term)
        yield tuple(tripleVals),binding
        
class InferredGoal(Exception): 
    def __init__(self, msg):
        self.msg = msg
    def __repr__(self):
        return "Goal inferred!: %"%self.msg         

class ReteNetwork:
    """
    The Rete network.  The constructor takes an N3 rule graph, an identifier (a BNode by default), an 
    initial Set of Rete tokens that serve as the 'working memory', and an rdflib Graph to 
    add inferred triples to - by forward-chaining via Rete evaluation algorithm), 
    """
    def __init__(self,ruleStore,name = None,
                 initialWorkingMemory = None, 
                 inferredTarget = None,
                 nsMap = {},
                 graphVizOutFile=None,
                 dontFinalize=False,
                 goal=None):
        self.leanCheck = {}
        self.goal = goal        
        self.nsMap = nsMap
        self.name = name and name or BNode()
        self.nodes = {}
        self.alphaPatternHash = {}
        self.ruleSet = set()
        for alphaPattern in xcombine(('1','0'),('1','0'),('1','0')):
            self.alphaPatternHash[tuple(alphaPattern)] = {}
        if inferredTarget is None:
            self.inferredFacts = Graph()
            namespace_manager = NamespaceManager(self.inferredFacts)
            for k,v in nsMap.items():
                namespace_manager.bind(k, v)    
            self.inferredFacts.namespace_manager = namespace_manager    
        else:            
            self.inferredFacts = inferredTarget
        self.workingMemory = initialWorkingMemory and initialWorkingMemory or set()
        self.proofTracers = {}
        self.terminalNodes  = set()
        self.instanciations = {}        
        start = time.time()
        self.ruleStore=ruleStore
        self.justifications = {}
        self.dischargedBindings = {}
        if not dontFinalize:
            self.ruleStore._finalize()
        self.filteredFacts = Graph()
        
        #'Universal truths' for a rule set are rules where the LHS is empty.  
        # Rather than automatically adding them to the working set, alpha nodes are 'notified'
        # of them, so they can be checked for while performing inter element tests.
        self.universalTruths = []
        from FuXi.Horn.HornRules import Ruleset
        self.rules=set()
        self.negRules = set()
        for rule in Ruleset(n3Rules=self.ruleStore.rules,nsMapping=self.nsMap):
            import warnings
            warnings.warn(
          "Rules in a network should be built *after* construction via "+
          " self.buildNetworkClause(HornFromN3(n3graph)) for instance",
                          DeprecationWarning,2)            
            self.buildNetworkFromClause(rule)
        self.alphaNodes = [node for node in self.nodes.values() if isinstance(node,AlphaNode)]
        self.alphaBuiltInNodes = [node for node in self.nodes.values() if isinstance(node,BuiltInAlphaNode)]
        self._setupDefaultRules()
        print >>sys.stderr,"Time to build production rule (RDFLib): %s seconds"%(time.time() - start)
        if initialWorkingMemory:            
            start = time.time()          
            self.feedFactsToAdd(initialWorkingMemory)
            print >>sys.stderr,"Time to calculate closure on working memory: %s m seconds"%((time.time() - start) * 1000)            
        if graphVizOutFile:
            print >>sys.stderr,"Writing out RETE network to ", graphVizOutFile
            renderNetwork(self,nsMap=nsMap).write(graphVizOutFile)
                        
    def getNsBindings(self,nsMgr):
        for prefix,Uri in nsMgr.namespaces():
            self.nsMap[prefix]=Uri

    def buildFilterNetworkFromClause(self,rule):
        lhs = BNode()
        rhs = BNode()
        builtins=[]
        for term in rule.formula.body:
            if isinstance(term, N3Builtin):
                #We want to move builtins to the 'end' of the body
                #so they only apply to the terminal nodes of 
                #the corresponding network
                builtins.append(term)
            else:
                self.ruleStore.formulae.setdefault(lhs,Formula(lhs)).append(term.toRDFTuple())
        for builtin in builtins:
            self.ruleStore.formulae.setdefault(lhs,Formula(lhs)).append(builtin.toRDFTuple())
        nonEmptyHead=False
        for term in rule.formula.head:
            nonEmptyHead=True
            assert not hasattr(term,'next')
            assert isinstance(term,Uniterm)
            self.ruleStore.formulae.setdefault(rhs,Formula(rhs)).append(term.toRDFTuple())
        assert nonEmptyHead,"Filters must conclude something!"
        self.ruleStore.rules.append((self.ruleStore.formulae[lhs],self.ruleStore.formulae[rhs]))
        tNode = self.buildNetwork(iter(self.ruleStore.formulae[lhs]),
                             iter(self.ruleStore.formulae[rhs]),
                             rule,
                             aFilter=True)
        self.alphaNodes = [node for node in self.nodes.values() if isinstance(node,AlphaNode)]
        self.rules.add(rule)
        return tNode
                        
    def buildNetworkFromClause(self,rule):
        lhs = BNode()
        rhs = BNode()
        builtins=[]
        for term in rule.formula.body:
            if isinstance(term, N3Builtin):
                #We want to move builtins to the 'end' of the body
                #so they only apply to the terminal nodes of 
                #the corresponding network
                builtins.append(term)
            else:
                self.ruleStore.formulae.setdefault(lhs,Formula(lhs)).append(term.toRDFTuple())
        for builtin in builtins:
            self.ruleStore.formulae.setdefault(lhs,Formula(lhs)).append(builtin.toRDFTuple())
        nonEmptyHead=False
        for term in rule.formula.head:
            nonEmptyHead=True
            assert not hasattr(term,'next')
            assert isinstance(term,Uniterm)
            self.ruleStore.formulae.setdefault(rhs,Formula(rhs)).append(term.toRDFTuple())
        if not nonEmptyHead:
            import warnings
            warnings.warn(
          "Integrity constraints (rules with empty heads) are not supported!: %s"%rule,
                          SyntaxWarning,2)            
            return
        self.ruleStore.rules.append((self.ruleStore.formulae[lhs],self.ruleStore.formulae[rhs]))
        tNode = self.buildNetwork(iter(self.ruleStore.formulae[lhs]),
                             iter(self.ruleStore.formulae[rhs]),
                             rule)
        self.alphaNodes = [node for node in self.nodes.values() if isinstance(node,AlphaNode)]
        self.rules.add(rule)
        return tNode
        
    def calculateStratifiedModel(self,database):
        """
        Stratified Negation Semantics for DLP using SPARQL to handle the negation
        """
        if not self.negRules:
            return
        from FuXi.DLP.Negation import StratifiedSPARQL
        from FuXi.Rete.Magic import PrettyPrintRule
        import copy
        noNegFacts = 0
        for i in self.negRules:
            #Evaluate the Graph pattern, and instanciate the head of the rule with 
            #the solutions returned
            nsMapping = dict([(v,k) for k,v in self.nsMap.items()])
            sel,compiler=StratifiedSPARQL(i,nsMapping)
            query=compiler.compile(sel)
            i.stratifiedQuery=query
            vars = sel.projection
            unionClosureG = self.closureGraph(database)
            for rt in unionClosureG.query(query):
                solutions={}
                if isinstance(rt,tuple):
                    solutions.update(dict([(vars[idx],i) for idx,i in enumerate(rt)]))
                else:
                    solutions[vars[0]]=rt
                i.solutions=solutions
                head=copy.deepcopy(i.formula.head)
                head.ground(solutions)
                fact=head.toRDFTuple()
                self.inferredFacts.add(fact)
                self.feedFactsToAdd(generateTokenSet([fact]))
                noNegFacts += 1
        #Now we need to clear assertions that cross the individual, concept, relation divide
        toRemove=[]
        for s,p,o in self.inferredFacts.triples((None,RDF.type,None)):
            if s in unionClosureG.predicates() or\
               s in [_s for _s,_p,_o in 
                        unionClosureG.triples_choices(
                                            (None,
                                             RDF.type,
                                             [OWL_NS.Class,
                                              OWL_NS.Restriction]))]:
                self.inferredFacts.remove((s,p,o))
        return noNegFacts
                        
    def setupDescriptionLogicProgramming(self,
                                         owlN3Graph,
                                         expanded=[],
                                         addPDSemantics=True,
                                         classifyTBox=False,
                                         constructNetwork=True,
                                         derivedPreds=[],
                                         ignoreNegativeStratus=False,
                                         safety = DATALOG_SAFETY_NONE):
        rt=[rule 
                    for rule in MapDLPtoNetwork(self,
                                                owlN3Graph,
                                                complementExpansions=expanded,
                                                constructNetwork=constructNetwork,
                                                derivedPreds=derivedPreds,
                                                ignoreNegativeStratus=ignoreNegativeStratus,
                                                safety = safety)]
        if ignoreNegativeStratus:
            rules,negRules=rt
            rules = set(rules)
            self.negRules = set(negRules)
        else:
            rules=set(rt)
        if constructNetwork:
            self.rules.update(rules)
        additionalRules = set(AdditionalRules(owlN3Graph))
        if addPDSemantics:
            from FuXi.Horn.HornRules import HornFromN3
            additionalRules.update(HornFromN3(StringIO(non_DHL_OWL_Semantics)))
        
        if constructNetwork:
            for rule in additionalRules:
                self.buildNetwork(iter(rule.formula.body),
                                  iter(rule.formula.head),
                                  rule)
                self.rules.add(rule)
        else:
            rules.update(additionalRules)
            
        if constructNetwork:
            rules = self.rules
            
        noRules=len(rules)
        if classifyTBox:
            self.feedFactsToAdd(generateTokenSet(owlN3Graph))
#        print "##### DLP rules fired against OWL/RDF TBOX",self
        return rules
    
    def reportSize(self,tokenSizeThreshold=1200,stream=sys.stdout):
        for pattern,node in self.nodes.items():
            if isinstance(node,BetaNode):
                for largeMem in itertools.ifilter(
                                   lambda i:len(i) > tokenSizeThreshold,
                                   node.memories.itervalues()):
                    if largeMem:
                        print >>stream, "Large apha node memory extent: "
                        pprint(pattern)
                        print >>stream, len(largeMem)        
    
    def reportConflictSet(self,closureSummary=False,stream=sys.stdout):
        tNodeOrder = [tNode 
                        for tNode in self.terminalNodes 
                            if self.instanciations.get(tNode,0)]
        tNodeOrder.sort(key=lambda x:self.instanciations[x],reverse=True)
        for termNode in tNodeOrder:
            print >>stream,termNode
            print >>stream,"\t", termNode.clauseRepresentation()
            print >>stream,"\t\t%s instanciations"%self.instanciations[termNode]
        if closureSummary:        
            print >>stream ,self.inferredFacts.serialize(format='turtle')
                
    def parseN3Logic(self,src):
        store=N3RuleStore(additionalBuiltins=self.ruleStore.filters)
        Graph(store).parse(src,format='n3')
        store._finalize()
        assert len(store.rules),"There are no rules passed in!"
        from FuXi.Horn.HornRules import Ruleset
        for rule in Ruleset(n3Rules=store.rules,
                            nsMapping=self.nsMap):
            self.buildNetwork(iter(rule.formula.body),
                              iter(rule.formula.head),
                              rule)
            self.rules.add(rule)
        self.alphaNodes = [node for node in self.nodes.values() if isinstance(node,AlphaNode)]
        self.alphaBuiltInNodes = [node for node in self.nodes.values() if isinstance(node,BuiltInAlphaNode)]        

    def __repr__(self):
        total = 0 
        for node in self.nodes.values():
            if isinstance(node,BetaNode):
                total+=len(node.memories[LEFT_MEMORY])
                total+=len(node.memories[RIGHT_MEMORY])
        
        return "<Network: %s rules, %s nodes, %s tokens in working memory, %s inferred tokens>"%(len(self.terminalNodes),len(self.nodes),total,len(self.inferredFacts))
        
    def closureGraph(self,sourceGraph,readOnly=True,store=None):
        if readOnly:
            if store is None and not sourceGraph:
                store = Graph().store
            store = store is None and sourceGraph.store or store
            roGraph=ReadOnlyGraphAggregate([sourceGraph,self.inferredFacts],
                                           store=store)
            roGraph.namespace_manager = NamespaceManager(roGraph)
            for srcGraph in [sourceGraph,self.inferredFacts]:
                for prefix,uri in srcGraph.namespaces():
                    roGraph.namespace_manager.bind(prefix,uri)
            return roGraph
        else:
            cg=ConjunctiveGraph()
            cg+=sourceGraph
            cg+=self.inferredFacts
            return cg        

    def _setupDefaultRules(self):
        """
        Checks every alpha node to see if it may match against a 'universal truth' (one w/out a LHS)
        """
        for node in self.nodes.values():
            if isinstance(node,AlphaNode):                
                node.checkDefaultRule(self.universalTruths)
        
    def clear(self):
        self.nodes = {}
        self.alphaPatternHash = {}
        self.rules = set()
        for alphaPattern in xcombine(('1','0'),('1','0'),('1','0')):
            self.alphaPatternHash[tuple(alphaPattern)] = {}
        self.proofTracers = {}
        self.terminalNodes  = set()
        self.justifications = {}
        self._resetinstanciationStats()
        self.workingMemory = set()
        self.dischargedBindings = {}
        
    def reset(self,newinferredFacts=None):
        "Reset the network by emptying the memory associated with all Beta Nodes nodes"
        for node in self.nodes.values():
            if isinstance(node,BetaNode):
                node.memories[LEFT_MEMORY].reset()
                node.memories[RIGHT_MEMORY].reset()
        self.justifications = {}
        self.proofTracers = {}
        self.inferredFacts = newinferredFacts if newinferredFacts is not None else Graph()
        self.workingMemory = set()
        self._resetinstanciationStats()        
                                
    def fireConsequent(self,tokens,termNode,debug=False):
        """
        
        "In general, a p-node also contains a specifcation of what production it corresponds to | the
        name of the production, its right-hand-side actions, etc. A p-node may also contain information
        about the names of the variables that occur in the production. Note that variable names
        are not mentioned in any of the Rete node data structures we describe in this chapter. This is
        intentional |it enables nodes to be shared when two productions have conditions with the same
        basic form, but with different variable names."        
        
        
        Takes a set of tokens and the terminal Beta node they came from
        and fires the inferred statements using the patterns associated
        with the terminal node.  Statements that have been previously inferred
        or already exist in the working memory are not asserted
        """
        if debug:
            print "%s from %s"%(tokens,termNode)

        newTokens = []
        termNode.instanciatingTokens.add(tokens)
        def iterCondition(condition):
            if isinstance(condition,Exists):
                return condition.formula
            return isinstance(condition,SetOperator) and condition or iter([condition])
        def extractVariables(term,existential=True):
            if isinstance(term,existential and BNode or Variable):
                yield term
            elif isinstance(term,Uniterm):
                for t in term.toRDFTuple():
                    if isinstance(t,existential and BNode or Variable):
                        yield t
        
        #replace existentials in the head with new BNodes!
        BNodeReplacement = {}
        for rule in termNode.rules:
            if isinstance(rule.formula.head,Exists):
                for bN in rule.formula.head.declare:
                    if not isinstance(rule.formula.body,Exists) or \
                       bN not in rule.formula.body.declare:
                       BNodeReplacement[bN] = BNode()
        for rhsTriple in termNode.consequent:
            if BNodeReplacement:
                rhsTriple = tuple([BNodeReplacement.get(term,term) for term in rhsTriple])
            if debug:
                if not tokens.bindings:
                    tokens._generateBindings()                    
            override,executeFn = termNode.executeActions.get(rhsTriple,(None,None))
            
            if override:
                #There is an execute action associated with this production
                #that is attaced to the given consequent triple and
                #is meant to perform all of the production duties
                #(bypassing the inference of triples, etc.)
                executeFn(termNode,None,tokens,None,debug)                    
            else:                
                for inferredTriple,binding in _mulPatternWithSubstitutions(tokens,rhsTriple,termNode):
                    if [term for term in inferredTriple if isinstance(term,Variable)]:
                        #Unfullfilled bindings (skip non-ground head literals)
                        if executeFn:
                            #The indicated execute action is supposed to be triggered
                            #when the indicates RHS triple is inferred for the
                            #(even if it is not ground)
                            executeFn(termNode,inferredTriple,tokens,binding,debug)                                        
                        continue
                    inferredToken=ReteToken(inferredTriple)
                    self.proofTracers.setdefault(inferredTriple,[]).append(binding)
                    self.justifications.setdefault(inferredTriple,set()).add(termNode)
                    if termNode.filter and inferredTriple not in self.filteredFacts:
                        self.filteredFacts.add(inferredTriple)
                    if inferredTriple not in self.inferredFacts and inferredToken not in self.workingMemory:                    
                        if debug:
                            print "Inferred triple: ", inferredTriple, " from ",termNode.clauseRepresentation()
                            inferredToken.debug = True
                        self.inferredFacts.add(inferredTriple)
                        self.addWME(inferredToken)
                        currIdx = self.instanciations.get(termNode,0)
                        currIdx+=1
                        self.instanciations[termNode] = currIdx
                        if executeFn:
                            #The indicated execute action is supposed to be triggered
                            #when the indicates RHS triple is inferred for the
                            #first time
                            executeFn(termNode,inferredTriple,tokens,binding,debug)
                        if self.goal is not None and self.goal in self.inferredFacts:
                           raise InferredGoal("Proved goal " + repr(self.goal))                    
                    else:
                        if debug:
                            print "Inferred triple skipped: ", inferredTriple
                        if executeFn:
                            #The indicated execute action is supposed to be triggered
                            #when the indicates RHS triple is inferred for the
                            #first time
                            executeFn(termNode,inferredTriple,tokens,binding,debug)
    
    def addWME(self,wme):
        """
        procedure add-wme (w: WME) exhaustive hash table versiong
            let v1, v2, and v3 be the symbols in the three fields of w
            alpha-mem = lookup-in-hash-table (v1,v2,v3)
            if alpha-mem then alpha-memory-activation (alpha-mem, w)
            alpha-mem = lookup-in-hash-table (v1,v2,*)
            if alpha-mem then alpha-memory-activation (alpha-mem, w)
            alpha-mem = lookup-in-hash-table (v1,*,v3)
            if alpha-mem then alpha-memory-activation (alpha-mem, w)
            ...
            alpha-mem = lookup-in-hash-table (*,*,*)
            if alpha-mem then alpha-memory-activation (alpha-mem, w)
        end        
        """
#        print wme.asTuple()       
        for termComb,termDict in iteritems(self.alphaPatternHash):
            for alphaNode in termDict.get(wme.alphaNetworkHash(termComb),[]):
#                print "\t## Activated AlphaNode ##"
#                print "\t\t",termComb,wme.alphaNetworkHash(termComb)
#                print "\t\t",alphaNode
                alphaNode.activate(wme.unboundCopy())
    
    def feedFactsToAdd(self,tokenIterator):
        """
        Feeds the network an iterator of facts / tokens which are fed to the alpha nodes 
        which propagate the matching process through the network
        """
        for token in tokenIterator:
            self.workingMemory.add(token)
            #print token.unboundCopy().bindingDict
            self.addWME(token)
    
    def _findPatterns(self,patternList):
        rt = []
        for betaNodePattern, alphaNodePatterns in \
            [(patternList[:-i],patternList[-i:]) for i in xrange(1,len(patternList))]:
            assert isinstance(betaNodePattern,HashablePatternList)
            assert isinstance(alphaNodePatterns,HashablePatternList)            
            if betaNodePattern in self.nodes:                                
                rt.append(betaNodePattern)
                rt.extend([HashablePatternList([aPattern]) for aPattern in alphaNodePatterns])
                return rt
        for alphaNodePattern in patternList:
            rt.append(HashablePatternList([alphaNodePattern]))
        return rt            
    
    def createAlphaNode(self,currentPattern):
        """
        """
        if isinstance(currentPattern,N3Builtin):
            node = BuiltInAlphaNode(currentPattern)
        else:
            node = AlphaNode(currentPattern,self.ruleStore.filters)
        self.alphaPatternHash[node.alphaNetworkHash()].setdefault(node.alphaNetworkHash(groundTermHash=True),[]).append(node)
        if not isinstance(node,BuiltInAlphaNode) and node.builtin:
            s,p,o = currentPattern
            node = BuiltInAlphaNode(N3Builtin(p,self.ruleStore.filters[p](s,o),s,o))
        return node
    
    def _resetinstanciationStats(self):
        self.instanciations = dict([(tNode,0) for tNode in self.terminalNodes])
        
    def checkDuplicateRules(self):
        checkedClauses={}
        for tNode in self.terminalNodes:
            for rule in tNode.rules:
                collision = checkedClauses.get(rule.formula)
                assert collision is None,"%s collides with %s"%(tNode,checkedClauses[rule.formula])
                checkedClauses.setdefault(tNode.rule.formula,[]).append(tNode)

    def registerReteAction(self,headTriple,override,executeFn):
        """
        Register the given execute function for any rule with the
        given head using the override argument to determine whether or
        not the action completely handles the firing of the rule.

        The signature of the execute action is as follows:

        def someExecuteAction(tNode, inferredTriple, token, binding):
            .. pass ..
        """
        for tNode in self.terminalNodes:
            for rule in tNode.rules:
                if not isinstance(rule.formula.head, Uniterm):
                    continue
                headTriple = rule.formula.head.toRDFTuple()
                tNode.executeActions[headTriple] = (override,executeFn)
    
    def buildNetwork(self,lhsIterator,rhsIterator,rule,aFilter=False):
        """
        Takes an iterator of triples in the LHS of an N3 rule and an iterator of the RHS and extends
        the Rete network, building / reusing Alpha 
        and Beta nodes along the way (via a dictionary mapping of patterns to the built nodes)
        """
        matchedPatterns   = HashablePatternList()
        attachedPatterns = []
        hasBuiltin = False
        LHS = []
        while True:
            try:
                currentPattern = lhsIterator.next()
                #The LHS isn't done yet, stow away the current pattern
                #We need to convert the Uniterm into a triple
                if isinstance(currentPattern,Uniterm):
                    currentPattern = currentPattern.toRDFTuple()
                LHS.append(currentPattern)
            except StopIteration:                
                #The LHS is done, need to initiate second pass to recursively build join / beta
                #nodes towards a terminal node                
                
                #We need to convert the Uniterm into a triple
                consequents = [isinstance(fact,Uniterm) and fact.toRDFTuple() or fact for fact in rhsIterator]
                if matchedPatterns and matchedPatterns in self.nodes:
                    attachedPatterns.append(matchedPatterns)
                elif matchedPatterns:
                    rt = self._findPatterns(matchedPatterns)
                    attachedPatterns.extend(rt)
                if len(attachedPatterns) == 1:
                    node = self.nodes[attachedPatterns[0]]
                    if isinstance(node,BetaNode):
                        terminalNode = node
                    else:
                        paddedLHSPattern = HashablePatternList([None])+attachedPatterns[0]                    
                        terminalNode = self.nodes.get(paddedLHSPattern)
                        if terminalNode is None:
                            #New terminal node
                            terminalNode = BetaNode(None,node,aPassThru=True)
                            self.nodes[paddedLHSPattern] = terminalNode    
                            node.connectToBetaNode(terminalNode,RIGHT_MEMORY)                            
                    terminalNode.consequent.update(consequents)
                    terminalNode.rules.add(rule)
                    terminalNode.antecedent = rule.formula.body
                    terminalNode.network    = self
                    terminalNode.headAtoms.update(rule.formula.head)
                    terminalNode.filter = aFilter
                    self.terminalNodes.add(terminalNode)                    
                else:              
                    moveToEnd = []
                    endIdx = len(attachedPatterns) - 1
                    finalPatternList = []
                    for idx,pattern in enumerate(attachedPatterns):
                        assert isinstance(pattern,HashablePatternList),repr(pattern)                    
                        currNode = self.nodes[pattern]
                        if (isinstance(currNode,BuiltInAlphaNode) or 
                            isinstance(currNode,BetaNode) and currNode.fedByBuiltin):
                            moveToEnd.append(pattern)
                        else:
                            finalPatternList.append(pattern)
                    terminalNode = self.attachBetaNodes(chain(finalPatternList,moveToEnd))
                    terminalNode.consequent.update(consequents)
                    terminalNode.rules.add(rule)
                    terminalNode.antecedent = rule.formula.body                    
                    terminalNode.network    = self
                    terminalNode.headAtoms.update(rule.formula.head)
                    terminalNode.filter = aFilter
                    self.terminalNodes.add(terminalNode)
                    self._resetinstanciationStats()                        
                #self.checkDuplicateRules()
                return terminalNode
            if HashablePatternList([currentPattern]) in self.nodes:
                #Current pattern matches an existing alpha node
                matchedPatterns.append(currentPattern)
            elif matchedPatterns in self.nodes:
                #preceding patterns match an existing join/beta node
                newNode = self.createAlphaNode(currentPattern)
                if len(matchedPatterns) == 1 and HashablePatternList([None])+matchedPatterns in self.nodes:
                    existingNode = self.nodes[HashablePatternList([None])+matchedPatterns]
                    newBetaNode = BetaNode(existingNode,newNode)     
                    self.nodes[HashablePatternList([None])+matchedPatterns+HashablePatternList([currentPattern])] = newBetaNode
                    matchedPatterns = HashablePatternList([None])+matchedPatterns+HashablePatternList([currentPattern])
                else:
                    existingNode = self.nodes[matchedPatterns]                
                    newBetaNode = BetaNode(existingNode,newNode)     
                    self.nodes[matchedPatterns+HashablePatternList([currentPattern])] = newBetaNode
                    matchedPatterns.append(currentPattern)
                
                self.nodes[HashablePatternList([currentPattern])] = newNode
                newBetaNode.connectIncomingNodes(existingNode,newNode)
                #Extend the match list with the current pattern and add it
                #to the list of attached patterns for the second pass                
                attachedPatterns.append(matchedPatterns)
                matchedPatterns = HashablePatternList()
            else:
                #The current pattern is not in the network and the match list isn't
                #either.  Add an alpha node 
                newNode = self.createAlphaNode(currentPattern)
                self.nodes[HashablePatternList([currentPattern])] = newNode
                #Add to list of attached patterns for the second pass
                attachedPatterns.append(HashablePatternList([currentPattern]))
                
    def attachBetaNodes(self,patternIterator,lastBetaNodePattern=None):
        """
        The second 'pass' in the Rete network compilation algorithm:
        Attaches Beta nodes to the alpha nodes associated with all the patterns
        in a rule's LHS recursively towards a 'root' Beta node - the terminal node
        for the rule.  This root / terminal node is returned
        """
        try:
            nextPattern = patternIterator.next()
        except StopIteration:
            assert lastBetaNodePattern
            if lastBetaNodePattern:
                return self.nodes[lastBetaNodePattern]
            else:
                assert len(self.universalTruths),"should be empty LHSs"
                terminalNode = BetaNode(None,None,aPassThru=True)
                self.nodes[HashablePatternList([None])] = terminalNode                
                return terminalNode#raise Exception("Ehh. Why are we here?")
        if lastBetaNodePattern:
            firstNode = self.nodes[lastBetaNodePattern]
            secondNode = self.nodes[nextPattern]
            newBNodePattern = lastBetaNodePattern + nextPattern
            newBetaNode = BetaNode(firstNode,secondNode)        
            self.nodes[newBNodePattern] = newBetaNode            
        else:            
            firstNode  = self.nodes[nextPattern]
            oldAnchor = self.nodes.get(HashablePatternList([None])+nextPattern)
            if not oldAnchor: 
                if isinstance(firstNode,AlphaNode):
                    newfirstNode = BetaNode(None,firstNode,aPassThru=True) 
                    newfirstNode.connectIncomingNodes(None,firstNode)
                    self.nodes[HashablePatternList([None])+nextPattern] = newfirstNode
                else:
                    newfirstNode = firstNode
            else:                
                newfirstNode = oldAnchor
            firstNode = newfirstNode
            secondPattern = patternIterator.next()
            secondNode = self.nodes[secondPattern]
            newBetaNode = BetaNode(firstNode,secondNode)                         
            newBNodePattern = HashablePatternList([None]) + nextPattern + secondPattern                    
            self.nodes[newBNodePattern] = newBetaNode

        newBetaNode.connectIncomingNodes(firstNode,secondNode)
        return self.attachBetaNodes(patternIterator,newBNodePattern)
    
def ComplementExpand(tBoxGraph,complementAnnotation):
    complementExpanded=[]
    for negativeClass in tBoxGraph.subjects(predicate=OWL_NS.complementOf):
        containingList = first(tBoxGraph.subjects(RDF.first,negativeClass))
        prevLink = None
        while containingList:
            prevLink = containingList
            containingList = first(tBoxGraph.subjects(RDF.rest,containingList))
        if prevLink:
            for s,p,o in tBoxGraph.triples_choices((None,
                                                [OWL_NS.intersectionOf,
                                                 OWL_NS.unionOf],
                                                 prevLink)):
                if (s,complementAnnotation,None) in tBoxGraph:
                    continue
                _class = Class(s)
                complementExpanded.append(s)
                print "Added %s to complement expansion"%_class
                ComplementExpansion(_class)
    
    
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()
    
