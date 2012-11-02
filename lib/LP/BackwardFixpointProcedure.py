# encoding: utf-8
"""
BackwardFixpointProcedure.py

.. A sound and complete query answering method for recursive databases
based on meta-interpretation called Backward Fixpoint Procedure ..

Uses RETE-UL as the RIF PRD implementation of a meta-interpreter of an
adorned ruleset that builds large, conjunctive (BGPs) SPARQL queries.

Facts are only generated in a bottom up evaluation of the interpreter if a
query has been issued for that fact or if an appropriate sub-query has been
generated.

Sub-queries for rule bodies are generated if a sub-query for the corresponding
rule head already exists. Sub-queries for conjuncts are generated from
sub-queries of conjunctions they appear in

Evaluate condition and ACTION:

Evaluate consults the already generated facts, and may take a single atom or a
conjunction as its argument, returning true if all of the conjuncts have
already been generated.

"""

import copy
import unittest
from io import StringIO
from pprint import pprint

from rdflib.graph import ReadOnlyGraphAggregate
from rdflib import (
    Literal,
    Namespace,
    RDF,
    Variable,
    URIRef,
    )
from rdflib.util import first

from FuXi.SPARQL import (
    ConjunctiveQueryMemoize,
    EDBQuery,
    EDBQueryFromBodyIterator,
    )
from FuXi.Rete.SidewaysInformationPassing import (
    GetArgs,
    GetVariables,
    SIPRepresentation,
    iterCondition,
    GetOp,
    )
from FuXi.Rete.BetaNode import ReteMemory, BetaNode, RIGHT_MEMORY, LEFT_MEMORY
from FuXi.Rete.AlphaNode import AlphaNode, ReteToken, BuiltInAlphaNode
from FuXi.Rete.Network import HashablePatternList, InferredGoal
from FuXi.Rete.Proof import MakeImmutableDict
from FuXi.Rete.Magic import AdornedRule, AdornedUniTerm  # , IsHybridPredicate
from FuXi.Rete.Util import generateTokenSet
from FuXi.Horn.HornRules import extractVariables, Clause
from FuXi.Rete.RuleStore import N3Builtin, FILTERS
from FuXi.Horn.PositiveConditions import (
    buildUniTerm,
    BuildUnitermFromTuple,
    And,
    Exists,
    Uniterm
    )
from functools import reduce


# From itertools recipes
def _iteritems(mapping):
    return zip(mapping.iterkeys(), mapping.itervalues())

BFP_NS = Namespace(
        'http://dx.doi.org/10.1016/0169-023X(90)90017-8#')
BFP_RULE = Namespace(
        'http://code.google.com/p/python-dlp/wiki/BFPSpecializedRule#')
HIGHER_ORDER_QUERY = BFP_RULE.SecondOrderPredicateQuery


class EvaluateConjunctiveQueryMemory(ReteMemory):
    """
    The extension of the evaluate predicate for a particular specialized rule

    "Whenever a new WME is filtered through the alpha network and reaches an
    alpha memory, we simply add it to the list of other WMEs in that memory,
    and inform each of the attached join nodes"

    A beta memory node stores a list of the tokens it contains, plus a list of
    its children (other nodes in the beta part of the network). Before we give
    its data structure, though, recall that we were going to do our procedure
    calls for left and right activations through a switch or case statement or
    a jumptable indexed according to the type of node being activated. Thus,
    given a (pointer to a) node, we need to be able to determine its type. This
    is straightforward if we use variant records to represent nodes. (A variant
    record is a record that can contain any one of several different sets of
    fields.) Each node in the beta part of the net will be represented by
    a rete-node structure:

    Whenever a beta memory is informed of a new match (consisting of an
    existing token and some WME), we build a token, add it to the list in the
    beta memory, and inform each of the beta memory's children:
    """

    def __init__(self, betaNode, memoryPos, _filter=None):
        super(EvaluateConjunctiveQueryMemory, self).__init__(
                                        betaNode, memoryPos, _filter)

    # def union(self, other):
    #     """Return the union of two sets as a new set.
    #
    #     (I.e. all elements that are in either set.)
    #     """
    #     result = ReteMemory(self.successor,self.position)
    #     result._update(other)
    #     return result

    def __repr__(self):
        return "<Evaluate Memory: %s item(s)>" % (len(self))

    # def addToken(self,token,debug=False): pass

    # def reset(self):
    #     self.clear()
    #     self.substitutionDict = {}


class MalformedQeryPredicate(Exception):
    """An exception raised when a malformed quer predicate is created"""
    def __init__(self, msg):
        super(MalformedQeryPredicate, self).__init__(msg)


# coroutine.py
#
# A decorator function that takes care of starting a coroutine
# automatically on call.

def coroutine(func):
    def start(*args, **kwargs):
        cr = func(*args, **kwargs)
        next(cr)
        return cr
    return start


class GoalSolutionAction(object):
    def getGroundTerms(self, literal):
        goalGroundTerms = {}
        for idx, term in enumerate(GetArgs(literal)):
            if not isinstance(term, Variable):
                goalGroundTerms[idx] = term
        return goalGroundTerms

    def __init__(self, bfp, varMap):
        self.goalGroundTerms = self.getGroundTerms(bfp.goal)
        self.bfp = bfp
        self.varMap = varMap
        self.solutionSet = set()
        # self.goal = BuildUnitermFromTuple(goal)

    def __repr__(self):
        stream = StringIO()
        return stream.getvalue()

    def __call__(self, tNode, inferredTriple, token, binding, debug):
        """
        Called when the BFP triggers a p-node associated with a goal
        , storing the solutions for later retrieval
        """
        if not self.goalGroundTerms or not [i_t for i_t in enumerate(GetArgs(BuildUnitermFromTuple(inferredTriple))) if self.goalGroundTerms.get(i_t[0],i_t[1]) != i_t[1]]:
            #Only contributes to goal if bound arguments correspond to those
            #bound in the goal literal
            if set(self.varMap).intersection(binding):
                #If there are variables to be mapped only consider those as solutions
                self.bfp.goalSolutions.add(
                    MakeImmutableDict(
                        dict(
                            [(self.varMap[key],binding[key])
                                for key in binding
                                  if key in self.varMap])))
            else:
                #If there are no variables to map, then pass on the bindings
                # as solution
                self.bfp.goalSolutions.add(MakeImmutableDict(binding))
            if self.bfp.debug:
                print("added %s to goal solutions"%binding)

class EvaluateExecution(object):
    """Handles the inference of evaluate literals in BFP"""
    def __init__(self, rnbi, bfp, termNodes):
        (ruleNo,bodyIdx) = rnbi
        self.ruleNo        = ruleNo
        self.bodyIdx       = bodyIdx
        self.bfp           = bfp
        self.termNodes     = termNodes
        for termNode in self.termNodes:
            assert [ (s,p,o)
                        for s,p,o in termNode.consequent
                            if p == BFP_NS.evaluate and \
                               s == BFP_RULE[str(self.ruleNo)] and \
                               o == Literal(self.bodyIdx) ],"%s %s"%(self,termNode)


    def __call__(self, tNode, inferredTriple, token, binding, debug):
        """
        Called when an evaluate literal is inferred and
        given the relevant bindings

        Add entailed evaluate bindings (as high-arity predicates)
        directly into RETE-UL beta node memories in a circular fashion
        propagating their sucessor
        """
        for s,p,o in tNode.consequent:
            if p == BFP_NS.evaluate:
                for memory in self.bfp.evalHash[(self.ruleNo,self.bodyIdx)]:
                    for bindings in token.bindings:
                        memory.addToken(token,debug)
                        if memory.position == LEFT_MEMORY:
                            memory.successor.propagate(memory.position,debug,token)
                        else:
                            memory.successor.propagate(None,debug,token)

    def __repr__(self):
        return "Evaluate(%s %s)"%(
                    self.ruleNo,
                    self.bodyIdx)
                    
class ProofDerivationStepAction(object):
    def __init__(self, bfp, headLiteral,ruleIdx,bodyIdx):
        self.bfp = bfp
        self.headLiteral = headLiteral
        self.ruleIdx = ruleIdx
        self.bodyIdx = bodyIdx
        self.subsequentActions = set()
        
    def __repr__(self):
        subsequentTypes = {}
        for act in self.subsequentActions:
            clsName = act.__class__.__name__
            subsequentTypes[clsName] = subsequentTypes.get(clsName,0) + 1
        return "Goal step for rule %s%s"%(
                    self.ruleIdx,
                    ', triggers %s'%(
                        ','.join([
                            '%s %ss'%(no,_type) for _type,no in list(subsequentTypes.items())])) 
                            if self.subsequentActions else '')
        
    def __call__(self, tNode, inferredTriple, token,    binding, debug=False):        
        #Rule a^k
        #p(x0,...,xn) :- And(query_p(x0,...,xn) evaluate(ruleNo,n,X))
        #Need two write into self.bfp.proofTrace: headLiteral, ruleIdx, bodyIdx, 1        
        for binding in token.bindings:
            _bindings = dict([(k,v) for k,v in list(binding.items()) 
                                if v != None])                
            lit=copy.deepcopy(self.headLiteral)
            lit.ground(_bindings)     
            self.bfp.proofTrace.append((lit,self.ruleIdx,self.bodyIdx+1,'G'))
            self.bfp.derivationMap.setdefault(lit,set()).add((self.ruleIdx,self.bodyIdx+1,'G'))
        for action in self.subsequentActions:
            action(tNode, inferredTriple, token, binding, debug)

class ProofAction(object):
    def __init__(self, bfp, bodyLiteral,ruleIdx,bodyIdx):
        self.bfp = bfp
        self.bodyLiteral = bodyLiteral
        self.ruleIdx = ruleIdx
        self.bodyIdx = bodyIdx
        self.subsequentActions = set()
        
    def __repr__(self):
        subsequentTypes = {}
        for act in self.subsequentActions:
            clsName = act.__class__.__name__
            subsequentTypes[clsName] = subsequentTypes.get(clsName,0) + 1
        return "Lemma step for rule %s%s"%(
                    self.ruleIdx,
                    ', triggers %s'%(
                        ','.join([
                            '%s %s(s)'%(no,_type) for _type,no in list(subsequentTypes.items())])) 
                            if self.subsequentActions else '')
                
    def __call__(self, tNode, inferredTriple, token,    binding, debug=False):        
        #Rule c^k
        #evaluate(ruleNo,j+1,X) :- evaluate(ruleNo,j,X), bodyLiteral
        #Need two write into self.bfp.proofTrace: bodyLiteral, ruleIdx, bodyIdx, 0      
        for binding in token.bindings:
            _bindings = dict([(k,v) for k,v in list(binding.items()) 
                                if v != None])                
            lit=copy.deepcopy(self.bodyLiteral)
            if isinstance(lit,AdornedUniTerm):
                lit = lit.convert2NormalUterm()
            lit.ground(_bindings)        
            triple=lit.toRDFTuple()
            self.bfp.proofTrace.append((lit,self.ruleIdx,self.bodyIdx+1,'SG'))
            if (self.ruleIdx,
                self.bodyIdx+1,
                'Q') not in [(step[0],step[1],step[2]) for step in self.bfp.derivationMap.get(triple,set())]:
                self.bfp.derivationMap.setdefault(lit,set()).add((self.ruleIdx,self.bodyIdx+1,'SG'))
        for action in self.subsequentActions:
            action(tNode, inferredTriple, token, binding, debug)            

class QueryExecution(object):
    """
    Called when an evaluate literal is inferred and
    given the relevant bindings
    """
    def __init__(self, bfp, queryLiteral,freeHeadVars,conjoinedTokenMem=None,edbConj=None,originPos=None):
        self.freeHeadVars = freeHeadVars
        self.factGraph = bfp.factGraph
        self.bfp = bfp
        self.queryLiteral = queryLiteral
        self.bfp.firedEDBQueries = set()
        self.edbConj = edbConj
        self.conjoinedTokenMem = conjoinedTokenMem
        self.originPos = originPos

    def __call__(self, tNode, inferredTriple, token,    binding, debug=False):
        """
        Called when a (EDB) query literal is triggered with
        given bindings.
        """
        assert len(tNode.consequent) == 1
        key = (self.queryLiteral,tNode,token)
        if key not in self.bfp.firedEDBQueries:
            self.bfp.firedEDBQueries.add(key)
            for binding in token.bindings:
                _bindings = dict([(k,v) for k,v in list(binding.items())
                                    if v != None])

                closure = ReadOnlyGraphAggregate([self.factGraph,
                                                  self.bfp.metaInterpNetwork.inferredFacts])
                closure.templateMap = self.factGraph.templateMap
                #For each mapping that unifies with theory
                if self.edbConj:
                    _vars = set()
                    for lit in self.edbConj:
                        _vars.update(list(GetVariables(lit,secondOrder=True)))
                    _qLit =EDBQuery([copy.deepcopy(lit) for lit in self.edbConj],
                                    self.factGraph,#closure,
                                    _vars,
                                    specialBNodeHandling=self.bfp.specialBNodeHandling)
                else:
                    _qLit = copy.deepcopy(self.queryLiteral)
                    _qLit =EDBQuery([_qLit],
                                    self.factGraph,#closure,
                                    list(
                                        GetVariables(_qLit,
                                                     secondOrder=True)),
                                    specialBNodeHandling=self.bfp.specialBNodeHandling)
                origQuery = _qLit.copy()
                _qLit.ground(_bindings)

                #The variables returned by the maximal, connected base component query
                #should be only for those needed for free variables in the rule head
                queryVars = reduce(
                    lambda l,r:l.union(r),
                    [set(GetVariables(item)) for item in _qLit.formulae]
                )
                #@TODO: Verify we don't always want to limit passing of
                # intermediate query answers to just those relevant to head solns
#                _qLit.returnVars = list(set(self.freeHeadVars).intersection(queryVars))

                if self.bfp.debug:
                    print("%sQuery triggered for "%(
                        ' maximal db conjunction '
                            if self.edbConj else ''), tNode.clauseRepresentation())
                    print(_qLit.asSPARQL())
                self.bfp.edbQueries.add(_qLit)
                queryVars = origQuery.getOpenVars()
                # tokens2Propagate=[
                #     t for t in token.tokens
                #         if [
                #             v for v in t.getVarBindings()
                #                 if v not in queryVars
                #         ]
                # ]
                isGround = not _qLit.returnVars
                rt = self.tabledQuery(_qLit)
                if isGround:
                    if first(rt):
                        self.handleQueryAnswer(origQuery,
                                               token,
                                               self.bfp.debug,
                                               _qLit,
                                               ({},binding))
                else:
                    for ans in rt:
                        if self.bfp.debug:
                            pprint(ans)
                        self.handleQueryAnswer(origQuery,
                                               token,
                                               self.bfp.debug,
                                               _qLit,
                                               (ans,binding))

    @ConjunctiveQueryMemoize()
    def tabledQuery(self,conjQuery):
        queryStr,rt = conjQuery.evaluate(self.bfp.debug)
        if isinstance(rt,bool):
            yield rt
        else:
            for item in rt:
                yield item

    def handleQueryAnswer(self,literal,token,debug,queryAtom,bindings=None):
        edbResult = literal.copy()
        if self.conjoinedTokenMem:
            assert bindings is not None
            #identify join variables amongst EDB query
            joinVars = set()
            def collectJoinVars(left,right):
                if isinstance(left,set):
                    #collection of vars on left, update commulative joinvar set
                    #with vars in right in this collection
                    rightVars = set()
                    for var in GetVariables(right,secondOrder=True):
                        if var in left:
                            joinVars.add(var)
                        rightVars.add(var)
                    return left.union(rightVars)
                else:
                    #left and right are base atoms, get their variables
                    #, update cummulative joinvar with the intersection
                    leftVars  = set([var
                                for var in GetVariables(left,secondOrder=True)])
                    rightVars = set([var
                                for var in GetVariables(right,secondOrder=True)])
                    _jVars = leftVars.intersection(rightVars)
                    joinVars.update(_jVars)
                    return _jVars
            baseAtoms = [ atom for atom in edbResult if isinstance(atom,Uniterm) ]

            #@@TODO augment baseAtoms with atoms formed from incoming tokens
            # baseAtoms.extend([BuildUnitermFromTuple(term.asTuple()) for term in token.tokens])

            if len(literal)==1:
                joinVars = set()
            else:
                reduce(collectJoinVars,baseAtoms)

            #clone partially instanciated token, add to eval memory, and propagate
            #the succesor join node
            tokenClone = token.copy()

            queryBindings,tokenBindings = bindings
            # toDo = []
            self.bfp.queryAtom2Answers.setdefault(queryAtom,set()).update(baseAtoms)
            for idx,fact in enumerate(baseAtoms):
                queryLiteral = copy.deepcopy(fact)
                fact.ground(tokenBindings)
                fact.ground(queryBindings)
                #If fact is not ground, then it corresponds to ground fact for
                #with 'intermediate' variables
                if not fact.isGround(): continue
                # assert fact.isGround()
                self.bfp.proofTrace.append((queryAtom,self.originPos[0]-1,self.originPos[-1],'Q'))
                self.bfp.derivationMap.setdefault(fact,set()
                    ).add((self.originPos[0],self.originPos[-1],'Q'))
                self.bfp.queryAnswer2Atom.setdefault(fact,set()).add(queryAtom)
                self.bfp.queryAtom2Answers.setdefault(queryAtom,set(fact))
                
                wme = ReteToken(tuple([ term for term in fact.toRDFTuple() ]),debug=debug)
                wmeCopy = copy.deepcopy(wme)
                for termComb,termDict in _iteritems(self.bfp.metaInterpNetwork.alphaPatternHash):
                    for alphaNode in termDict.get(wmeCopy.alphaNetworkHash(termComb),[]):
                        validBNodes = []
                        for bNode in alphaNode.descendentBetaNodes:
                            _ruleIdx = int(
                                    list(
                                        list(
                                            bNode.rules)[0].formula.body
                                    )[0].arg[0][-1])
                            if _ruleIdx == self.originPos[0]:
                                validBNodes.append(bNode)
                        alphaNode.activate(wmeCopy,explicitSuccessors2Activate=validBNodes)
                        wmeCopy = copy.deepcopy(wme)
                wme.bindVariables(AlphaNode(queryLiteral.toRDFTuple()))
                tokenClone.tokens.add(wme)
            tokenClone.joinedBindings = dict([(key,token.joinedBindings[key])
                for key in joinVars.intersection(set(token.joinedBindings))])
            tokenClone._generateHash()
            tokenClone._generateBindings()
            for memory in self.associatedBetaMemories():
                memory.addToken(tokenClone,debug)
                if memory.position == LEFT_MEMORY:
                    memory.successor.propagate(
                        memory.position,
                        debug,
                        tokenClone)
                else:
                    memory.successor.propagate(
                        None,
                        debug,
                        tokenClone)

        else:
            if bindings:
                edbResult.ground(bindings)
            assert len(edbResult) == 1
            inferredToken=ReteToken(edbResult.formulae[0].toRDFTuple(),debug=debug)
            if inferredToken not in self.bfp.metaInterpNetwork.workingMemory:
                # if self.bfp.debug or debug:
                #     print "\tAnswer to BFP triggered query %s : %s"%(edbResult,bindings)
                self.bfp.metaInterpNetwork.addWME(inferredToken)

    def associatedBetaMemories(self):
        return self.bfp.evalHash[self.conjoinedTokenMem]

    def __repr__(self):
        return "QueryExecution%s%s"%('( against EDB: %s )'%(
         EDBQuery(self.edbConj,
                  self.factGraph) if self.edbConj else self.queryLiteral ),
         ' -> %s'%(repr(self.conjoinedTokenMem)) if self.conjoinedTokenMem else '')

def SetupEvaluationBetaNode(existingBetaNode,rule,network):
    """
    Take a BetaNode (and a BFP rule) that joins values from an evaluate condition
    with other conditions and replace the alpha node (and memory) used
    to represent the condition with a pass-thru beta with no parent nodes
    but whose right memory will be used to add bindings instanciated
    from evaluate assertions in the BFP algorithm

      Rete Network
      ------------

       ...
         \     memory <-- evalAlphaNode
          \   /
         existingBetaNode


          evalMemory <-- evaluate(ruleNo,bodyPos,vars)
           /
      existingBetaNode
    """
    #Delete the existing alpha node (and memory) for the evaluate condition

    newMem = EvaluateConjunctiveQueryMemory(existingBetaNode,RIGHT_MEMORY)
    existingBetaNode.memories[RIGHT_MEMORY] = newMem
    evalAlphaNode = existingBetaNode.rightNode
    network.alphaPatternHash[evalAlphaNode.alphaNetworkHash()][
        evalAlphaNode.alphaNetworkHash(groundTermHash=True)].remove(evalAlphaNode)
    network.alphaNodes.remove(evalAlphaNode)
    for mem in evalAlphaNode.descendentMemory:
        del mem
    pattern = HashablePatternList([evalAlphaNode.triplePattern])
    if pattern  in network.nodes:
        del network.nodes[pattern]
    del evalAlphaNode
    existingBetaNode.rightNode = None

    #The common variables are those in the original rule intersected
    #with those in the left node of the successor
    existingBetaNode.rightVariables = set(rule.declare)
    existingBetaNode.commonVariables = [
            leftVar for leftVar in existingBetaNode.leftVariables
                        if leftVar in existingBetaNode.rightVariables]
    return newMem


def NoopCallbackFn(termNode,inferredTriple,tokens,debug=False):
    pass

OPEN_QUERY_VARIABLE = BFP_NS.NonDistinguishedVariable

class BackwardFixpointProcedure(object):
    """
    Uses RETE-UL as a production rule system implementation of
    a meta-interpreter of an adorned RIF Core ruleset that builds solves conjunctive (BGPs)
    SPARQL queries.

    Facts are only generated in a bottom up evaluation of the interpreter if a
    query has been issued for that fact or if an appropriate sub-query has been generated.
    Sub-queries for rule bodies (conditions) are generated if a sub-query for
    the corresponding rule head already exists. Sub-queries for conjuncts are
    generated from sub-queries of conjunctions they appear in (queries are collected).
    """
    def __init__(self,
                factGraph,
                network,
                derivedPredicates,
                goal,
                sipCollection = [],
                hybridPredicates = None,
                debug = False,
                specialBNodeHandling = None,
                proofTrace = None):
        self.proofTrace            = []
        self.derivationMap         = {}
        self.queryAnswer2Atom      = {}
        self.queryAtom2Answers     = {}
        self.specialBNodeHandling  = specialBNodeHandling
        self.debug                 = debug
        self.metaRule2Network      = {}
        self.pushDownQueries       = {}
        self.maxEDBFront2End       = {}
        self.queryPredicates       = set()
        self.sipCollection         = sipCollection
        self.goal                  = BuildUnitermFromTuple(goal)
        self.factGraph             = factGraph
        self.rules                 = list(factGraph.adornedProgram)
        self.discardedRules        = set()
        self.ruleLabels            = {}
        self.bfpLookup             = {}
        self.actionHash            = {}
        self.namespaces = {
            u'bfp'  : BFP_NS,
            u'rule' : BFP_RULE
        }
        self.metaInterpNetwork = network
        self.derivedPredicates = set(derivedPredicates) if \
           isinstance(derivedPredicates,list) else derivedPredicates
        self.hybridPredicates      = hybridPredicates if hybridPredicates else []
        self.hybridPredicateRuleNos = set()
        self.edbQueries            = set()
        self.goalSolutions         = set()
        self.evalHash   = {}
        self.actionHash = {}
        self.productions= {}

    def answers(
        self,
        debug = False,
        solutionCallback = NoopCallbackFn):
        """
        Takes a conjunctive query, a sip collection
        and initiates the meta-interpreter for a given
        goal (at a time), propagating evaluate procedures
        explicitely if no bindings are given from the query
        to trigger subsequent subqueries via EDB predicates

        @TODO:
        Add a PRD externally defined action to the
        production of rules that produce answers
        for the query predicate.
        The action is a user specified callback that can be used
        to signal InferredGoal and halt RETE/UL evaluation prematurely
        otherwise, it is left to reach a stable state and the
        answers collected along the way are added and returned

        """
        # solutions = []

        # queryOp = GetOp(self.goal)
        if self.goal.isGround():
            #Mark ground goal so, production rule engine
            #halts when goal is inferred
            self.metaInterpNetwork.goal = self.goal.toRDFTuple()

        adornment = ['f' if isinstance(v,Variable) else 'b'
                        for v in GetArgs(self.goal,
                                         secondOrder=True)]
        adornment = reduce(lambda x,y:x+y,adornment)
        adornedQuery = AdornedUniTerm(self.goal,adornment)
        bfpTopQuery = self.makeDerivedQueryPredicate(adornedQuery)
        if debug:
            print("Asserting initial BFP query %s" % bfpTopQuery)

        assert bfpTopQuery.isGround()
        #Add BFP query atom to working memory, triggering procedure
        try:
            self.metaInterpNetwork.feedFactsToAdd(
                                generateTokenSet(
                                    [bfpTopQuery.toRDFTuple()],
                                        debugTriples=[bfpTopQuery.toRDFTuple()]
                                            if debug else []
                                    ))
        except InferredGoal:
            if debug:
                print("Reached ground goal. Terminated BFP!")
            return True
        else:
            if self.goal.isGround():
                #Ground goal, but didn't trigger it, response must be negative
                return False
                
    def extractProof(self,binding,ruleNo,inferredTriple,applyBindings=False):
        rule              = self.rules[ruleNo]
        ruleSipGraph      = rule.sip
        # for stuff in SIPRepresentation(ruleSipGraph): print stuff
        if not applyBindings:
            #Need to get bindings by unifying ground fact with head of rule
            _lit=copy.deepcopy(rule.formula.head)
            binding = _lit.unify(buildUniTerm(inferredTriple))
        lemmas=[]
        
        nonSipBindings = None
        #Iterate over subgoals 
        for idx,lit in enumerate(iterCondition(rule.formula.body)):
            #Ground subgoal using bindings to determine the ground
            #subgoal whose proof we need to (recursively) extract
            lit = copy.deepcopy(lit) 
            lit.ground(binding)
            if isinstance(lit,AdornedUniTerm):
                #A derived goal, so there must be one or more rules that were used to derive
                #it, so we search for instanciations of rules for this derived goal
                derivations = [entry for entry in self.derivationMap.get(lit,set()) if entry[2] =='G']
                if not len(derivations): 
                    #This doesn't match a Goal (G) step, so we must work the EDB query along
                    #a 'SIP walk'
                    from FuXi.DLP import LloydToporTransformation
                    #Collect a list of rules that match the adornment and predicate of current subgoal
                    matchingRuleIndices=set()
                    for _idx,_rule in enumerate(self.rules):
                        for clause in LloydToporTransformation(_rule.formula):
                            head=isinstance(clause.head,Exists) and clause.head.formula or clause.head
                            headPredicate = GetOp(head)
                            if compareAdornedPredToRuleHead(lit,head,self.hybridPredicates) and (
                                head.adornment == lit.adornment):
                                matchingRuleIndices.add(_idx)
                    validEntries=[]
                    for _ruleIdx in matchingRuleIndices:
                        _r = self.rules[_ruleIdx]
                        #For every (matching) rule, scan
                        #for rule instanciations 
                        for entry,value in list(self.derivationMap.items()):
                            if [i for i in value 
                                 if i[2] in ['G','Q']] and GetOp(entry) == GetOp(lit):
                                #Derivation entry corresponds to this rule 
                                #Extract proof tree
                                sols = lit.unify(entry)
                                matches = []
                                if idx < len(list(iterCondition(rule.formula.body))):
                                    nextBody = copy.deepcopy(list(iterCondition(rule.formula.body))[idx+1])
                                    nextBody.ground(sols)
                                    # _inner = self.extractProof(lit.unify(entry),_ruleIdx,nextBody.toRDFTuple())
                                    matches = [
                                        ([arg for argIdx,arg in enumerate(GetArgs(k)) 
                                            if not isinstance(arg,Variable) and 
                                               arg == list(GetArgs(nextBody))[argIdx]],
                                          k,
                                          v,
                                          nextBody.unify(k)) 
                                            for k,v in list(self.derivationMap.items()) 
                                                if GetOp(k) == GetOp(nextBody)]
                                    for matchingArgs,provedFact,steps,_sols in matches:
                                        if matchingArgs:
                                            validEntries.append((entry,sols,value))
                    for groundFact,_sols,_proofsInfo in validEntries:
                        nonSipBindings = _sols
                        assert len(_proofsInfo)==1
                        foundSoln = False
                        for _rIdx,_bodyPos,_stepType in _proofsInfo:
                            assert not foundSoln
                            if _stepType == 'Q':
                                lemmas.append((groundFact,'N/A','EDB Query',[],_sols))
                            elif derivations:
                                lemmas.append(self.extractProof(sols,int(derivations[0][0]),lit.toRDFTuple()))
                            else:
                                lemmas.append(self.extractProof(sols,int(_rIdx),groundFact.toRDFTuple()))
                            foundSoln = True
                else:
                    #Add to the list of lemmas (each of which correponds to a derived subgoal)
                    #the proof for the subgoal by calling extractProof recursively on the
                    #ground subgoal
                    lemmas.append(self.extractProof(binding,int(derivations[0][0]),lit.toRDFTuple()))
            else:
                if nonSipBindings is not None:
                    lit.ground(nonSipBindings)
                for subGoal in self.derivationMap.get(lit,set()):
                    if subGoal[2]=='Q':
                        lemmas.append((lit,'Via EDB Query',[],binding))
        assert len(lemmas) == len(list(iterCondition(rule.formula.body)))
        return (buildUniTerm(inferredTriple),
                rule,
                # ', '.join(SIPRepresentation(ruleSipGraph)),
                lemmas,
                binding)

    def specializeConjuncts(self,rule, idx, evalVars):
        """
        Extends the (vanilla) meta-interpreter for magic set and alexander rewriting
        sip strategies with capabilities for collapsing chains of extensional
        predicate queries (frames whose attributes are in EDB and externally-defined
        predicates) into a single SPARQL query
        """
        # _len = len(rule.formula.body)
        body = list(iterCondition(rule.formula.body))

        skipMDBQCount = 0
        for bodyIdx,bodyLiteral in enumerate(body):
            conjunct = []
            #V_{j} = V_{j-1} UNION vars(Literal(..)) where j <> 0
            evalVars[(idx+1,bodyIdx+1)] = list(GetVariables(bodyLiteral,secondOrder=True)) +\
                                               evalVars[(idx+1,bodyIdx)]
            pattern = HashablePatternList(
                [(BFP_RULE[str(idx+1)],
                  BFP_NS.evaluate,
                  Literal(bodyIdx))])
            pattern2 = HashablePatternList(
                [None,
                    (BFP_RULE[str(idx+1)],
                     BFP_NS.evaluate,
                     Literal(bodyIdx)),
                 bodyLiteral.toRDFTuple()])
            if skipMDBQCount > 0:
                #body literals in base connected components have
                #c^k meta rules with no-op actions
                termNodeCk = self.metaInterpNetwork.nodes[pattern2]
                key = (BFP_RULE[str(idx+1)],BFP_NS.evaluate,Literal(bodyIdx+1))
                assert key not in termNodeCk.executeActions
                def noOpAction(tNode, inferredTriple, token, binding, debug=False): pass
                termNodeCk.executeActions[key] = (True,noOpAction)
                skipMDBQCount -= 1
                continue

            # remainingBodyList = body[bodyIdx+1:] if bodyIdx+1<_len else []
            conjunct = EDBQueryFromBodyIterator(
                        self.factGraph,
                        rule.formula.body.formulae[bodyIdx:],
                        self.derivedPredicates,
                        self.hybridPredicates)

            
            lazyBaseConjunct = conjunct
            aNodeDk = self.metaInterpNetwork.nodes[pattern]

            #Rule d^k
            #query_Literal(x0,...,xj) :- evaluate(ruleNo,j,X)
            #query invokation
            tNode = first(aNodeDk.descendentBetaNodes)
            assert len(aNodeDk.descendentBetaNodes) == 1
            newEvalMemory = SetupEvaluationBetaNode(tNode,rule,self.metaInterpNetwork)

            isBase = bodyLiteral.adornment is None if \
                        isinstance(bodyLiteral,AdornedUniTerm) else True
            if isinstance(bodyLiteral,N3Builtin):
                if aNodeDk in self.metaInterpNetwork.alphaNodes:
                    self.metaInterpNetwork.alphaNodes.remove(aNodeDk)
                # evalTerm = (BFP_RULE[str(idx+1)],BFP_NS.evaluate,Literal(bodyIdx))
                del aNodeDk

                executeAction = EvaluateExecution((idx+1,bodyIdx),self,[])
                builtInNode = self.metaRule2Network[self.bfpLookup[('c',idx+1,bodyIdx+1)]]
                assert isinstance(builtInNode.rightNode,BuiltInAlphaNode)
                builtInNode.executeActions[bodyLiteral.toRDFTuple()] = (True,executeAction)

                #We bypass d^k, so when evaluate(ruleNo,j,X) is inferred
                #it is added to left memory of pNode associated with c^k
                self.evalHash.setdefault((idx+1,bodyIdx),[]).append(builtInNode.memories[LEFT_MEMORY])

                self.actionHash.setdefault((idx+1,bodyIdx+1),set()).add(builtInNode)
            elif conjunct and (isBase or lazyBaseConjunct):
                singleConj = EDBQuery([copy.deepcopy(item) for item in conjunct],
                                       self.factGraph)
                matchingTriple = first(tNode.consequent)
                assert len(tNode.consequent)==1
                newAction=QueryExecution(
                        self,
                        bodyLiteral,
                        list(rule.formula.head.getDistinguishedVariables(
                            varsOnly=True,
                            bound=False)),
                        conjoinedTokenMem = self.maxEDBFront2End[(idx+1,bodyIdx+1)]
                            if lazyBaseConjunct else None,
                        edbConj = conjunct if lazyBaseConjunct else singleConj,
                        originPos=(idx,bodyIdx+1))
                        

                self.evalHash.setdefault((idx+1,bodyIdx),[]).append(newEvalMemory)
                #If the body predicate is a 2nd order predicate, we don't infer the
                #second order query predicate (since it will trigger a query into
                #the EDB and thus there is no need to trigger subsequent rules)
                if matchingTriple in tNode.executeActions: 
                    existingAction = tNode.executeActions[matchingTriple][-1]
                    assert isinstance(executeAction,ProofAction)
                    executeAction.subsequentActions.add(newAction)
                else:
                    tNode.executeActions[matchingTriple] = (True,newAction)
            else:
                self.evalHash.setdefault((idx+1,bodyIdx),[]).append(newEvalMemory)
            if GetOp(bodyLiteral) not in FILTERS:# IsHybridPredicate(bodyLiteral,self.hybridPredicates) or ((GetOp(bodyLiteral) in self.derivedPredicates) and \
#                not (isBase and len(conjunct)>1)):
                assert pattern2 in self.metaInterpNetwork.nodes
                termNodeCk = self.metaInterpNetwork.nodes[pattern2]
                #Rule c^k
                #evaluate(ruleNo,j+1,X) :- evaluate(ruleNo,j,X), bodyLiteral
                if not isBase or not len(conjunct):
                    #We only associate an evaluate (or proof trace) action
                    # if this is *not* part of a connected base component
                    self.actionHash.setdefault((idx+1,bodyIdx+1),set()).add(termNodeCk)

                    #We only associate a evaluate action if this is *not*
                    #part of a connected base component
                    proofAction=ProofAction(self,bodyLiteral,idx,bodyIdx)

                    key = (BFP_RULE[str(idx+1)],BFP_NS.evaluate,Literal(bodyIdx+1))
                    assert key not in termNodeCk.executeActions
                    termNodeCk.executeActions[key] = (False,proofAction)
                else:
                    key = (BFP_RULE[str(idx+1)],BFP_NS.evaluate,Literal(bodyIdx+1))
                    assert key not in termNodeCk.executeActions
                    def noOpAction(tNode, inferredTriple, token, binding, debug=False): pass
                    termNodeCk.executeActions[key] = (True,noOpAction)

                assert isinstance(termNodeCk.rightNode,AlphaNode)
                termNodeCk.leftVariables = set(evalVars[(idx+1,bodyIdx)])
                termNodeCk.rightVariables = set(GetVariables(bodyLiteral,secondOrder=True))
                termNodeCk.commonVariables = termNodeCk.rightVariables.intersection(termNodeCk.leftVariables)
            if lazyBaseConjunct and len(conjunct)>1:
                endIdx = self.maxEDBFront2End[(idx+1,bodyIdx+1)][-1]
                skipMDBQCount = endIdx - bodyIdx - 1


    def checkNetworkWellformedness(self):
        for key,rule in list(self.bfpLookup.items()):
            if len(key) == 2:
                ruleType,ruleIdx = key
                bodyIdx = None
            else:
                ruleType,ruleIdx,bodyIdx = key

            termNode = self.metaRule2Network[rule]
            headTuple = rule.formula.head.toRDFTuple()

            # p(..) :- q_1(..), q_2(..), ..., q_n(..)
            if GetOp(rule.formula.head) == BFP_NS.evaluate:
                # evaluate(..,..) :-

                override,executeFn = termNode.executeActions.get(
                                          headTuple,
                                          (None,None))
                assert override and isinstance(executeFn,EvaluateExecution),termNode
                assert executeFn.ruleNo  == ruleIdx
                assert executeFn.bodyIdx == headTuple[-1]
                assert bodyIdx is None or executeFn.bodyIdx == int(bodyIdx),bodyIdx

                if isinstance(rule.formula.body,And):
                    # c^{ruleIdx}_{bodyIdx}
                    # evaluate(..,j+1) :- evaluate(..,j), q_{j+1}(..)
                    #@@ force check builtins or derived predicate c rules
                    if isinstance(termNode.leftNode,AlphaNode):
                        # alphaNode = termNode.leftNode
                        betaNode  = termNode.rightNode
                        assert isinstance(termNode.memories[RIGHT_MEMORY],
                                          EvaluateConjunctiveQueryMemory),termNode
                        assert isinstance(betaNode,BetaNode)
                    elif not termNode.fedByBuiltin:
                        # alphaNode = termNode.rightNode
                        betaNode  = termNode.leftNode

                        assert isinstance(termNode.memories[LEFT_MEMORY],
                                          EvaluateConjunctiveQueryMemory) or\
                               self.evalHash[(ruleIdx,bodyIdx-1)][0].successor != termNode,\
                               termNode
                        assert isinstance(betaNode,BetaNode)
                else:
                    # b^{ruleIdx}
                    # evaluate(..,j+1) :- query-p(..)
                    assert termNode.aPassThru

            elif isinstance(rule.formula.body,And):
                # a^{ruleIdx}
                # p(..) :- query-p(..), evaluate(..,n)
                assert isinstance(termNode.memories[RIGHT_MEMORY],
                                  EvaluateConjunctiveQueryMemory)
            else:
                # d^{ruleIdx}_{bodyIdx}
                # query-q_{j+1}(..) :- evaluate(..,j)
                queryLiteral = list(iterCondition(self.rules[ruleIdx-1].formula.body))[bodyIdx-1]
                if isinstance(queryLiteral,N3Builtin):
                    headTuple = queryLiteral.toRDFTuple()
                    executeKind = EvaluateExecution
                else:
                    executeKind = QueryExecution
                if GetOp(queryLiteral) not in self.derivedPredicates:
                    override,executeFn = termNode.executeActions.get(
                                              headTuple,
                                              (None,None))
                    assert override and isinstance(executeFn,executeKind),\
                      "%s %s %s"%(termNode.consequent,termNode.executeActions,termNode)
                    if not isinstance(queryLiteral,N3Builtin):
                        assert executeFn.queryLiteral == queryLiteral
                        #self.bfp.evalHash[self.conjoinedTokenMem]
                        assert executeFn.conjoinedTokenMem[0] == int(ruleIdx),\
                        "%s %s %s"%(termNode,executeFn,key)

    def createTopDownReteNetwork(self,debug=False,derivedSuffix='derived',vizNetwork=None,nodes=None,edges=None):
        """
        Uses the specialized BFP meta-interpretation rules to build a RETE-UL decision
        network that is modified to support the propagation of bindings from the evaluate
        predicates into a supplimental magic set sip strategy and the generation of subqueries.
        The end result is a bottom-up simulation of SLD resolution with complete, sound, and safe
        memoization in the face of recursion
        """
        for idx,rule in enumerate(self.rules):
            from FuXi.Rete.Magic import IsHybridPredicateRule
            if IsHybridPredicateRule(rule,derivedSuffix=derivedSuffix):
                if idx+1 not in self.hybridPredicateRuleNos:
                    self.hybridPredicateRuleNos.add(idx+1)
        for rule in set(self.specializeAdornedRuleset(debug)):
            self.metaRule2Network[rule] = \
               self.metaInterpNetwork.buildNetworkFromClause(rule)
        if debug:
            def ruleIdx(ruleKey):
                return ruleKey[1]
            def sortBFPRules(item1,item2):
                if ruleIdx(item1) != ruleIdx(item2):
                    return 1 if ruleIdx(item1) > ruleIdx(item2) else -1 if ruleIdx(item1) < ruleIdx(item2) else 0
                elif len(item1) == len(item2) and len(item1) == 3 and ruleIdx(item1) == ruleIdx(item2) and item1[-1] != item2[-1]:
                    return 1 if item1[-1] > item2[-1] else -1
                elif len(item1) > len(item2):
                    ruleKind,ruleNo = item2
                    if ruleKind == 'a':
                        return -1
                    else:
                        return  1
                elif len(item1) < len(item2):
                    ruleKind,ruleNo = item1
                    if ruleKind == 'a':
                        return  1
                    else:
                        return -1
                elif len(item1) == 3:
                    ruleKind1,bodyIdx1,ruleNo1 = item1
                    ruleKind2,bodyIdx1,ruleNo2 = item2
                    if ruleKind1 == 'c' and ruleKind2 == 'd':
                        return  1
                    else:
                        return -1
                elif len(item1) == 2:
                    return -1 if item1[0] == 'b' else 1 if item1[0] == 'a' else 0
                else:
                    raise Exception('problems comparing %s and %s'%(item1,item))
            sortedBFPRules =[
                str("%s : %s")%(key,self.bfpLookup[key])
                    for key in sorted(self.bfpLookup,
#                                     key=lambda items: str(items[1])+items[0],
                                      cmp=sortBFPRules)]
            for _ruleStr in sortedBFPRules:
                print(_ruleStr)
        evalVars        = {}
        for idx,rule in enumerate(self.rules):
            if rule in self.discardedRules:
                continue

            # label = BFP_RULE[str(idx+1)]
            conjunctLength = len(list(iterCondition(rule.formula.body)))

            #Rule a^k
            #p(x0,...,xn) :- And(query_p(x0,...,xn) evaluate(ruleNo,n,X))
            currentPattern = HashablePatternList([(BFP_RULE[str(idx+1)],
                                                   BFP_NS.evaluate,
                                                   Literal(conjunctLength))])
            assert rule.declare
            #Find alpha node associated with evaluate condition
            node = self.metaInterpNetwork.nodes[currentPattern]
            #evaluate(k,n,X) is a condition in only 1 bfp rule
            assert len(node.descendentBetaNodes) == 1
            bNode = first(node.descendentBetaNodes)
            assert bNode.leftNode.aPassThru
            assert len(bNode.consequent) == 1
            newEvalMemory = SetupEvaluationBetaNode(bNode,rule,self.metaInterpNetwork)
            self.evalHash.setdefault((idx+1,conjunctLength),[]).append(newEvalMemory)

            
            
            if vizNetwork:
                existingBetaNode.commonVariables
                if bNode not in nodes:
                    _len=len(nodes)
                    nodes[_len]=bNode
                    attrs = [
                        ('shape', 'circle'),
                        ('label', ','.join([v.n3() 
                            for v in existingBetaNode.commonVariables]))]
                    vizNetwork.add_node(_len,attrs)
                    # if bNode.memories[RIGHT_MEMORY] not in nodes:
                    #     nodes.add(bNode.memories[RIGHT_MEMORY])
                    #     attrs = [
                    #         ('shape', 'circle'),
                    #         ('label', ','.join([v.n3() 
                    #             for v in existingBetaNode.commonVariables]))]
                    #     vizGraph.add_node(bNode.identifier)
            if GetOp(rule.formula.head) == GetOp(self.goal):
                #This rule matches a goal, add a solution collecting action
                
                goalSolutionAction = GoalSolutionAction(
                        self,
                        rule.formula.head.getVarMapping(self.goal))
                        
                        
                proofAction=ProofDerivationStepAction(self,rule.formula.head,idx,conjunctLength)
                proofAction.subsequentActions.add(goalSolutionAction)
                bNode.executeActions[rule.formula.head.toRDFTuple()] = (False,proofAction)                        
                bNode.ruleNo = idx
            else:
                proofAction=ProofDerivationStepAction(self,rule.formula.head,idx,conjunctLength)
                bNode.executeActions[rule.formula.head.toRDFTuple()] = (False,proofAction)
                        

            self.productions.setdefault(GetOp(rule.formula.head),[]).append((idx,bNode))

            #Rule b^k
            #evaluate(ruleNo,0,X) :- query_p(x0,...,xn)
            _rule = self.bfpLookup[('b',idx+1)]
            #alpha node associated with query predicate for head of original rule
            _bodyAlphaNode = self.metaInterpNetwork.nodes[
                    HashablePatternList([_rule.formula.body.toRDFTuple()])]

            assert len(_bodyAlphaNode.descendentBetaNodes)==1
            tNode = first(_bodyAlphaNode.descendentBetaNodes)
            self.actionHash.setdefault((idx+1,0),set()).add(tNode)

            
            if vizNetwork and tNode not in nodes:
                _len=len(nodes)
                nodes[_len]=tNode                
                attrs = [
                    ('shape', 'circle'),
                    ('label', ','.join([v.n3() 
                        for v in tNode.commonVariables]))]
                vizNetwork.add_node(_len,attrs)
            
            #V_{0} = vars(query_p(..))
            headQueryPred = list(iterCondition(_rule.formula.body))[0]
            try:
                evalVars[(idx+1,0)] = list(headQueryPred.terms)
            except IndexError:
                raise
                self.discardedRules.add(rule)
                continue

            self.specializeConjuncts(rule, idx, evalVars)

        for (ruleNo,bodyIdx),tNodes in list(self.actionHash.items()):
            #Attach evaluate action to p-node that propagates
            #token to beta memory associated with evaluate(ruleNo,bodyIdx)
            executeAction = EvaluateExecution((ruleNo,bodyIdx),
                                              self,
                                              tNodes)
            evaluationStmt = (BFP_RULE[str(ruleNo)],BFP_NS.evaluate,Literal(bodyIdx))
            for tNode in tNodes:
                eAct = tNode.executeActions.get(evaluationStmt)
                if eAct and isinstance(eAct[-1],ProofAction): 
                    existingAction = eAct[-1]
                    existingAction.subsequentActions.add(executeAction)
                    tNode.executeActions[evaluationStmt] = (True,existingAction)
                else:
                    tNode.executeActions[evaluationStmt] = (True,executeAction)
                # executeAction = EvaluateExecution(evalHash,(idx+1,bodyIdx+1),self,termNodeCk)
                # assert len(termNodeCk.consequent)==1
                # termNodeCk.executeAction = (None,executeAction)

        #Fix join variables for BetaNodes involving evaluate predicates
        for idx,rule in enumerate(self.rules):
            if rule in self.discardedRules:
                continue

            #Rule a^k
            #p(x0,...,xn) :- And(query_p(x0,...,xn) evaluate(ruleNo,n,X))
            #Join vars = vars(query_p) AND V_{n}
            headQueryPred = self.bfpLookup[('b',idx+1)].formula.body
            ruleBodyLen = len(list(iterCondition(rule.formula.body)))
            termNode  = first(self.evalHash[idx+1,ruleBodyLen]).successor
            termNode.commonVariables = list(set(evalVars[(idx+1,ruleBodyLen)]
                                       ).intersection(
                                           GetVariables(headQueryPred,
                                                        secondOrder=True)))
                                                        
            if vizNetwork and termNode not in nodes:
                _len=len(nodes)
                nodes[_len]=termNode                
                attrs = [
                    ('shape', 'circle'),
                    ('label', ','.join([v.n3() 
                        for v in termNode.commonVariables]))]
                vizNetwork.add_node(_len,attrs)
                                                        
            skipMDBQCount = 0
            for bodyIdx,bodyLiteral in enumerate(iterCondition(rule.formula.body)):
                if skipMDBQCount > 0:
                    skipMDBQCount -= 1
                    continue

                if (idx+1,bodyIdx+1)  in self.actionHash:
                    #Rule c^k
                    #evaluate(ruleNo,j+1,X) :- And(evaluate(ruleNo,j,X) Literal(x0,...,xj))
                    #Join vars = vars(Literal) AND V_{j}
                    termNode2 = self.actionHash[(idx+1,bodyIdx+1)]
                    assert len(termNode2)==1
                    termNode2 = first(termNode2)
                    termNode2.commonVariables = list(set(evalVars[(idx+1,bodyIdx)]
                                               ).intersection(
                                                   GetVariables(bodyLiteral,
                                                                secondOrder=True)))                                                                
                    if vizNetwork and termNode2 not in nodes:
                        _len=len(nodes)
                        nodes[_len]=termNode2                        
                        attrs = [
                            ('shape', 'circle'),
                            ('label', ','.join([v.n3() 
                                for v in termNode2.commonVariables]))]
                        vizNetwork.add_node(_len,attrs)
                    
                if (idx+1,bodyIdx+1) in self.maxEDBFront2End:
                    endIdx = self.maxEDBFront2End[(idx+1,bodyIdx+1)][-1]
                    skipMDBQCount = endIdx - bodyIdx - 1

    def makeDerivedQueryPredicate(self,predicate):
        if isinstance(predicate,AdornedUniTerm):
            newAdornedPred=BFPQueryTerm(predicate,predicate.adornment)
        elif isinstance(predicate,N3Builtin):
            newAdornedPred=BFPQueryTerm(predicate,builtin=predicate)
        else:
            newAdornedPred=BFPQueryTerm(predicate,None)
        if isinstance(newAdornedPred,Uniterm):
            if isinstance(GetOp(newAdornedPred),Variable):
                newAdornedPred.setOperator(HIGHER_ORDER_QUERY)
            newAdornedPred.finalize()
        self.queryPredicates.add(newAdornedPred)
        return newAdornedPred

    def specializeAdornedRuleset(self,debug=False):
        """
        Specialization is applied to the BFP meta-interpreter with respect to the
        rules of the object program. For each rule of the meta-interpreter
        that includes a premise referring to a rule of the object program, one
        specialized version is created for each rule of the object program.

        """
        rules = set()
        for idx,rule in enumerate(self.rules):
            label = BFP_RULE[str(idx+1)]
            ruleBodyLen = len(list(iterCondition(rule.formula.body)))

            # if rule.isSecondOrder():
            #     if debug:
            #         print "Skipping second order rule (%s): %s"%(idx+1,rule)
            #     continue
            if debug:
                print("\t%s. %s"%(idx+1,rule))
                for _sip in SIPRepresentation(rule.sip):
                    print("\t\t%s" % _sip)
            newRule1 =self.rule1(rule,label,ruleBodyLen)
            self.bfpLookup[('a',idx+1)] = newRule1
            rules.add(newRule1)
            newRule2=self.rule2(rule,label,ruleBodyLen)
            self.bfpLookup[('b',idx+1)] = newRule2
            rules.add(newRule2)

            #indicate no skipping is ongoing
            skipMDBQCount = -1
            mDBConjFront = None
            # _len = len(rule.formula.body)
            for bodyIdx,bodyLiteral in enumerate(iterCondition(rule.formula.body)):
                bodyPredSymbol = GetOp(bodyLiteral)
                evaluateTerm = Uniterm(BFP_NS.evaluate,[label,Literal(bodyIdx+1)],
                    newNss=self.namespaces)
                priorEvaluateTerm = Uniterm(BFP_NS.evaluate,[label,Literal(bodyIdx)],
                    newNss=self.namespaces)
                if skipMDBQCount > 0:
                    skipMDBQCount -= 1
                    newRule = self.makeAdornedRule(
                        And([priorEvaluateTerm,
                             bodyLiteral]),
                        evaluateTerm)
                    self.bfpLookup[('c',idx+1,bodyIdx+1)] = newRule
                    rules.add(newRule)
                    continue
                elif skipMDBQCount == 0:
                    #finished skipping maximal db conjuncts, mark end of skipped
                    #conjuncts and indicate that no skipping is ongoing
                    self.maxEDBFront2End[mDBConjFront] = (idx+1,bodyIdx)
                    mDBConjFront = None
                    skipMDBQCount = -1

                conj = EDBQueryFromBodyIterator(
                            self.factGraph,
                            rule.formula.body.formulae[bodyIdx:],
                            self.derivedPredicates,
                            self.hybridPredicates)
                if conj:
                    #There is a maximal db conjunction, indicate skipping of rules involving
                    #conjuncts
                    mDBConjFront = (idx+1,bodyIdx+1)
                    if len(conj)>1:
                        skipMDBQCount = len(conj)-1
                        self.pushDownQueries[mDBConjFront] = EDBQuery([
                                    copy.deepcopy(item)
                                        for item in conj],self.factGraph)
                    else:
                        self.maxEDBFront2End[mDBConjFront] = (idx+1,bodyIdx+1)
                    if debug and skipMDBQCount>0:
                        print("maximal db query: %s" % self.pushDownQueries[mDBConjFront])
                        print("skipping %s literals, starting from the %s" % (
                            bodyIdx+1,skipMDBQCount))
                    if len(conj)+bodyIdx == len(rule.formula.body):
                        #maximal db conjunction takes up rest of body
                        #tokens should go into (k,n) - where n is the body length
                        self.maxEDBFront2End[mDBConjFront] = (idx+1,len(rule.formula.body))
                newRule = self.makeAdornedRule(
                                        And([priorEvaluateTerm,bodyLiteral]),
                                             evaluateTerm)
                self.bfpLookup[('c',idx+1,bodyIdx+1)] = newRule
                rules.add(newRule)
                if bodyPredSymbol in FILTERS and len(conj) > 2:
                    raise NotImplementedError(repr(rule))
                if bodyPredSymbol not in FILTERS:
                    #query_Literal(x0,...,xj) :- evaluate(ruleNo,j,X)
                    #OpenQuery(query_Literal)
                    newRule = self.makeAdornedRule(
                                priorEvaluateTerm,
                                self.makeDerivedQueryPredicate(bodyLiteral))
                    self.bfpLookup[('d',idx+1,bodyIdx+1)] = newRule
                    rules.add(newRule)
        return rules


    def makeAdornedRule(self, body, head):
        allVars = set()
        # first we identify body variables
        # @FIXME: unused variables
        bodyVars = set(reduce(lambda x,y:x+y,
                              [ list(extractVariables(i,existential=False))
                                        for i in iterCondition(body) ]))
        # then we identify head variables
        headVars = set(reduce(lambda x,y:x+y,
                              [ list(extractVariables(i,existential=False))
                                        for i in iterCondition(head) ]))

        return AdornedRule(Clause(body, head), declare=allVars)


    def rule1(self,rule,label,bodyLen):
        """
        'Facts are only generated in a bottom up evaluation of the interpreter if a query has been issued
         for that fact or if an appropriate sub-query has been generated by the metainterpreter
         itself.'

        a^{k}

        p(x0,...,xn) :- And(query_p(x0,...,xn) evaluate(ruleNo,n,X))
                            OpenQuery(query_p)

        If there are no bindings posed with the query, then OpenQuery(query_p)
        is used instead of query_p(x0,...,xn), indicating that there are no bindings
        but we wish to evaluate this derived predicate.  However, despite the fact
        that it has no bindings, we want to continue to (openly) solve predicates
        in a depth-first fashion until we hit an EDB query.

        """
        evaluateTerm = Uniterm(BFP_NS.evaluate,
                               [label,
                                Literal(bodyLen)],
                               newNss=self.namespaces)
        return self.makeAdornedRule(
                And([self.makeDerivedQueryPredicate(rule.formula.head),
                     evaluateTerm]),rule.formula.head)

    def rule2(self,rule,label,bodyLen):
        """
        When a query is matched, collect answers (begin to evaluate)

        b^{k}

        evaluate(ruleNo,0,X) :- query_p(x0,...,xn)
                                OpenQuery(query_p)

        If there are no bindings posed with the query, then OpenQuery(query_p)
        is used instead of query_p(x0,...,xn), indicating that there are no bindings
        but we wish to evaluate this derived predicate.  However, despite the fact
        that it has no bindings, we want to continue to (openly) solve predicates
        in a depth-first fashion until we hit an EDB query.

        """
        evaluateTerm = Uniterm(BFP_NS.evaluate,[label,Literal(0)],
                               newNss=self.namespaces)
        return self.makeAdornedRule(self.makeDerivedQueryPredicate(rule.formula.head),evaluateTerm)


class BFPQueryTerm(Uniterm):
    def __init__(self,uterm,adornment=None,naf = False,builtin = None):
        self.adornment=adornment
        self.nsMgr=uterm.nsMgr if hasattr(uterm,'nsMgr') else None
        if builtin:
            newArgs=[builtin.argument,builtin.result]
            op = builtin.uri
            self.builtin = builtin
        else:
            newArgs=copy.deepcopy(uterm.arg)
            op = uterm.op
            self.builtin = None
        super(BFPQueryTerm, self).__init__(op,newArgs,naf=naf)

    def clone(self):
        return BFPQueryTerm(self,self.adornment,self.naf)

    def _recalculateHash(self):
        self._hash=hash(reduce(lambda x,y:str(x)+str(y),
            len(self.arg)==2 and self.toRDFTuple() or [self.op]+self.arg))

    def __hash__(self):
        if self.adornment is None:
            return self._hash
        else:
            return self._hash ^ hash(reduce(lambda x,y:x+y,self.adornment))

    def finalize(self):
        if self.adornment:
            if self.hasBindings():
                if len(self.adornment) == 1:
                    #adorned predicate occurrence with one out of two arguments bound
                    #convert: It becomes a unary predicate
                    #(an rdf:type assertion)
                    self.arg[-1] = URIRef(GetOp(self)+'_query_'+first(self.adornment))
                    self.arg[0] = first(self.getDistinguishedVariables())
                    self.op = RDF.type
                elif ''.join(self.adornment) == 'bb':
                    #Two bound args
                    self.setOperator(URIRef(self.op+'_query_bb'))
                else:
                    #remove unbound argument, and reduce arity
                    singleArg = first(self.getDistinguishedVariables())
                    self.arg[-1] = URIRef(GetOp(self)+'_query_'+''.join(self.adornment))
                    self.arg[0]  = singleArg
                    self.op = RDF.type

            else:
                currentOp = GetOp(self)
                self.op = RDF.type
                self.arg = [currentOp,BFP_RULE.OpenQuery]
        else:
            if GetOp(self) != HIGHER_ORDER_QUERY:
                self.setOperator(URIRef(GetOp(self)+'_query'))
        self._recalculateHash()

    def hasBindings(self):
        if self.adornment:
            for idx,term in enumerate(GetArgs(self)):
                if self.adornment[idx]=='b':
                    return True
            return False

    def getDistinguishedVariables(self,varsOnly=False):
        if self.op == RDF.type:
            for idx,term in enumerate(GetArgs(self)):
                if self.adornment[idx] in ['b','fb','bf']:
                    if not varsOnly or isinstance(term,Variable):
                        yield term
        else:
            for idx,term in enumerate(self.arg):
                if self.adornment[idx]=='b':
                    if not varsOnly or isinstance(term,Variable):
                        yield term

    def getBindings(self,uniterm):
        rt={}
        for idx,term in enumerate(self.arg):
            goalArg=self.arg[idx]
            candidateArg=uniterm.arg[idx]
            if self.adornment is None or (self.adornment[idx]=='b' and isinstance(candidateArg,Variable)):
                #binding
                rt[candidateArg]=goalArg
        return rt

    def __repr__(self):
        if self.builtin:
            return repr(self.builtin)
        else:
            pred = self.normalizeTerm(self.op)
            if self.op == RDF.type:
                adornSuffix = ''# if self.adornment is None else '_'+self.adornment[0]
            else:
                adornSuffix= ''# if self.adornment is None else '_'+''.join(self.adornment)
            if self.op == RDF.type:
                return "%s%s(%s)"%(self.normalizeTerm(self.arg[-1]),
                                   adornSuffix,
                                   self.normalizeTerm(self.arg[0]))
            else:
                return "%s%s(%s)"%(pred,
                                     adornSuffix,
                                     ' '.join([self.normalizeTerm(i)
                                                for i in self.arg]))


class BackwardFixpointProcedureTests(unittest.TestCase):
    def setUp(self):
        pass


if __name__ == '__main__':
    unittest.main()
