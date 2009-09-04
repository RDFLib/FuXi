#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Implements a Sip-Strategy formed from a basic graph pattern and a RIF-Core ruleset
as a series of top-down derived SPARQL evaluations against a fact graph, 
generating a PML proof tree in the process.

Native Prolog-like Python implementation for RIF-Core, OWL, and SPARQL  
"""

import itertools, copy
from FuXi.Rete.AlphaNode import ReteToken
from FuXi.Horn.HornRules import Clause, Ruleset, Rule, HornFromN3
from FuXi.Horn.PositiveConditions import *
from FuXi.Rete.Proof import *
from rdflib.Graph import ReadOnlyGraphAggregate
from rdflib import URIRef, RDF, Namespace, Variable
from rdflib.util import first
from SidewaysInformationPassing import *

def PrepareSipCollection(adornedRuleset):
    """
    Takes adorned ruleset and returns an RDF dataset
    formed from the sips associated with each adorned
    rule as named graphs.  Also returns a mapping from
    the head predicates of each rule to the rules that match
    it - for efficient retrieval later
    """
    headToRule = {}
    graphs = []
    for rule in adornedRuleset:
        headToRule.setdefault(GetOp(rule.formula.head),set()).add(rule)
        graphs.append(rule.sip)
    if not graphs:
        return
    graph = ReadOnlyGraphAggregate(graphs)
    graph.headToRule = headToRule
    return graph

def getBindingsFromLiteral(groundTuple,ungroundLiteral):
    """
    Takes a ground fact and a query literal and returns
    the mappings from variables in the query literal
    to terms in the ground fact
    """
    ungroundTuple = ungroundLiteral.toRDFTuple()
    return ImmutableDict([(term,groundTuple[idx]) 
                  for idx,term in enumerate(ungroundTuple)
                      if isinstance(term,Variable) and
                         not isinstance(groundTuple[idx],Variable)])

def tripleToTriplePattern(graph,triple):
    return "%s %s %s"%tuple([renderTerm(graph,term) 
                                for term in triple])

def renderTerm(graph,term):
    if term == RDF.type:
        return ' a '
    else:
        try:
            return isinstance(term,BNode) and term.n3() or graph.qname(term)
        except:
            return term.n3()

def RunQuery(subQueryJoin,bindings,factGraph,isGround=False,vars=None):
    assert isGround or vars
    if not subQueryJoin:
        return False
    queryType = isGround and "ASK" or "SELECT %s"%(' '.join([v.n3() for v in vars]))
    subquery = "%s { %s }"%(queryType,' .\n'.join([tripleToTriplePattern(factGraph,
                                                          goal) 
                              for goal in subQueryJoin ]))
    rt = factGraph.query(subquery,
                             initNs = dict([(prefix, nsUri) 
                                  for prefix, nsUri in factGraph.namespaces()]),
                             initBindings=bindings)    
    if isGround:
        return subquery,rt.askAnswer[0]
    else:
        rt = len(vars)>2 and [ dict([(vars[idx],i) 
                                       for idx,i in enumerate(v)]) 
                                            for v in rt ] \
               or [ dict([(vars[0],v)]) for v in rt ]
        return subquery,rt
    
def lazyCollapseBooleanProofs(left,right):
    """
    Function for reduce that (lazily) performs
    boolean conjunction operator on a list
    of 2-tuples, a boolean value and some object
    . The boolean conjunction is applied on the
    first item in each 2-tuple
    """
    (leftBool,leftNode)   = left
    (rightBool,rightNode) = right
    if not leftBool:  
        return False, None
    else: 
        return (leftBool and rightBool) and (True,rightNode) or (False,None)
                
def literalIsGround(literal):
    """
    Whether or not the given literal has
    any variables for terms
    """
    return not [term for term in GetArgs(literal,
                                         secondOrder=True)
                                         if isinstance(term,Variable) ]
    
def mergeMappings1To2(mapping1,mapping2,makeImmutable=False):
    """
    Mapping merge.  A 'safe' update (i.e., if the key
    exists and the value is different, raise an exception)
    An immutable mapping can be returned if requested
    """
    newMap = {}
    for k,v in mapping1.items():
        val2 = mapping2.get(k)        
        if val2:
            assert v == val2 
            continue
        else: 
            newMap[k] = mapping1[k]
    newMap.update(mapping2)
    return makeImmutable and MakeImmutableDict(newMap) or newMap
         
class RuleFailure(Exception): pass 

def invokeRule(priorAnswers,
               bodyLiteralIterator,
               sip,
               otherargs,
               priorBooleanGoalSuccess=False,
               step = None):
    """
    Continue invokation of rule using (given) prior answers and list of remaining
    body literals (& rule sip).  If prior answers is a list, computation is split 
    disjunctively
    
    [..] By combining the answers to all these subqueries, we generate
    answers for the original query involving the rule head
    
    Also takes a PML step and updates it as it navigates the top-down proof
    tree (passing it on and updating it where necessary)

    """
    assert step is not None
    sipCollection, factGraph, derivedPreds, processedRules = otherargs 
    if len(priorAnswers)>1:
        #There are multiple answers in this step, we need to call invokeRule
        #recursively for each answer, returning the first positive attempt
        success = False
        for priorAns in priorAnswers:
            try:
                newStep = InferenceStep(step.parent,
                                        step.rule,
                                        source=step.source)
                newStep.antecedents = [ant for ant in step.antecedents]
                rt,_step\
                  =invokeRule([priorAns],
                              iter([i for i in bodyLiteralIterator]),
                              sip,
                              otherargs,
                              priorBooleanGoalSuccess,
                              newStep)
                if rt:
                    success = True
                    break                
            except RuleFailure: 
                pass
        return success, _step
    else:
        #Continue processing rule body condition
        #one literal at a time
        try:
            bodyLiteral = bodyLiteralIterator.next()
        except StopIteration:
            #Finished processing rule
            if priorAnswers:
                #Return the most recent (cumulative) answers and the given step
                return priorAnswers[-1], step
            elif priorBooleanGoalSuccess:
                #The prior subgoal bottomed out into
                #a success, so we continue
                pass#return True, step
            else:
                raise RuleFailure()
#        print "\t== invokeRule(%s,%s) =="%(priorAnswers,bodyLiteral)
        
        projectedBindings = priorAnswers and first(priorAnswers) or {}
        #For every body literal, subqueries are generated according to the sip      
        sipArcPred = URIRef(GetOp(bodyLiteral)+'_'+'_'.join(GetArgs(bodyLiteral)))
        assert len(list(IncomingSIPArcs(sip,sipArcPred)))<2
        subquery = copy.deepcopy(bodyLiteral)
        subquery.ground(projectedBindings)
        for N,x in IncomingSIPArcs(sip,sipArcPred):
            #That is, each subquery contains values for the bound arguments
            #that are passed through the sip arcs entering the node 
            #corresponding to that literal
            
            #projectedBindings = project(projectedBindings,x)
            
            #Create query out of body literal and apply sip-provided bindings
            subquery = copy.deepcopy(bodyLiteral)
            subquery.ground(projectedBindings)
            
        if literalIsGround(subquery):
            #subquery is ground, so there will only be boolean answers
            #we return the conjunction of the answers for the current
            #subquery
            answer,ns = reduce(
                            lazyCollapseBooleanProofs,
                            SipStrategy(subquery.toRDFTuple(),
                                        sipCollection,
                                        factGraph,
                                        derivedPreds,
                                        MakeImmutableDict(projectedBindings),
                                        processedRules,
                                        network = step.parent.network))
            if answer:
                #positive answer means we can continue processing the rule body
                step.antecedents.append(ns)
                return invokeRule(priorAnswers,
                                  bodyLiteralIterator,
                                  sip,
                                  otherargs,
                                  True,
                                  step)
            else:
                #negative answer means the invokation of the rule fails
                raise RuleFailure()
        else:
            answers = list(
                    SipStrategy(subquery.toRDFTuple(),
                                sipCollection,
                                factGraph,
                                derivedPreds,
                                MakeImmutableDict(projectedBindings),
                                processedRules,
                                network = step.parent.network))
            #solve (non-ground) subgoal
            combinedAnswers = []
            for ans,ns in answers:
                #Accumulate the answers
                assert isinstance(ans,dict)
                combinedAnswers.append(mergeMappings1To2(ans,
                                                         projectedBindings,
                                                         makeImmutable=True))
            if not answers:
                raise RuleFailure()
            else:
                goals = set([g for a,g in answers])
                assert len(goals)==1
                step.antecedents.append(goals.pop())
                return invokeRule(combinedAnswers,
                                  bodyLiteralIterator,
                                  sip,
                                  otherargs,
                                  priorBooleanGoalSuccess,
                                  step)
      
def SipStrategy(query,
                sipCollection,
                factGraph,
                derivedPreds,
                bindings={},
                processedRules = None,
                network = None):
    """
    Accordingly, we define a sip-strategy for computing the answers to a query 
    expressed using a set of Datalog rules, and a set of sips, one for each 
    adornment of a rule head, as follows...
    """
    queryLiteral = BuildUnitermFromTuple(query)
    processedRules = processedRules and processedRules or set()
    if bindings:
        #There are bindings.  Apply them to the terms in the query
        queryLiteral.ground(bindings)
        
    if queryLiteral in processedRules:
        #Moinization
        yield False,None        
    else: 
        isGround = literalIsGround(queryLiteral)
        
        ns=NodeSet(queryLiteral.toRDFTuple(),
                   network=network,
                   identifier=BNode())    
        
        adornedProgram = factGraph.adornedProgram    
        queryPred = GetOp(queryLiteral)
        #For every rule head matching the query, we invoke the rule, 
        #thus determining an adornment, and selecting a sip to follow
        rules = sipCollection.headToRule.get(queryPred,set())
    
        #maintained list of rules that haven't been processed before and
        #match the query
        validRules = []
        
        #each subquery contains values for the bound arguments that are passed 
        #through the sip arcs entering the node corresponding to that literal. For
        #each subquery generated, there is a set of answers.
        answers = []
            
        #for rule in rules.difference(processedRules):
        for rule in rules:
            #An exception is the special predicate ph; it is treated as a base 
            #predicate and the tuples in it are those supplied for qb by unification.
            headBindings = getBindingsFromLiteral(queryLiteral.toRDFTuple(),
                                                  rule.formula.head)
            comboBindings = dict([(k,v) for k,v in itertools.chain(
                                                      bindings.items(),
                                                      headBindings.items())])
            if [term for term in rule.formula.head.getDistinguishedVariables()
                    if term not in headBindings]:
                continue
            subQueryAnswers = []
            dontStop = True
            projectedBindings = comboBindings.copy()
            try:
                #Invoke the rule
                step = InferenceStep(ns,rule.formula)
                rt,step\
                  =invokeRule([headBindings],
                              iter(iterCondition(rule.formula.body)),
                              rule.sip,
                              (sipCollection, 
                               factGraph, 
                               derivedPreds,
                               processedRules.union([queryLiteral])), 
                               #processedRules.union([(headBindings,rule)])),
                              step=step)
                if rt:
                    if isinstance(rt,dict):
                        #We received a mapping and must rewrite it via
                        #correlation between the variables in the rule head
                        #and the variables in the original query (after applying 
                        #bindings) 
                        varMap = rule.formula.head.getVarMapping(queryLiteral)
                        passedMap = {}
                        for inVar,outVar in varMap.items(): 
                            passedMap[outVar]=rt[inVar]
                        rt = MakeImmutableDict(passedMap)
                        step.bindings = rt
                    else:
                        step.bindings = headBindings
                    validRules.append(rule)
                    ns.steps.append(step)
                    yield rt, ns 
                
            except RuleFailure:
                #Clean up failed antecedents
                if ns in step.antecedents:
                    step.antecedents.remove(ns)
    
        if not validRules:
            #No rules matching, query factGraph for answers
            factStep = InferenceStep(ns,source='some RDF graph')
            ns.steps.append(factStep)
            if not isGround:
                subquery,rt=RunQuery([queryLiteral.toRDFTuple()],
                                 bindings,
                                 factGraph,
                                 False,
                                 [v for v in GetArgs(queryLiteral,
                                                     secondOrder=True) 
                                                     if isinstance(v,Variable)])
                factStep.groundQuery = subquery
                for ans in rt:
                    factStep.bindings.update(ans)
                    yield ans, ns
            else:
                #All the relevant derivations have been explored and the result
                #is a ground query we can directly execute against the facts
                factStep.bindings.update(bindings)
                subquery,rt = RunQuery([queryLiteral.toRDFTuple()],
                                    bindings,
                                    factGraph,
                                    True)
                factStep.groundQuery = subquery
                yield rt,ns
