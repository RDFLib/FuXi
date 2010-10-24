#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Implements a Sip-Strategy formed from a basic graph pattern and a RIF-Core ruleset
as a series of top-down derived SPARQL evaluations against a fact graph, 
generating a walk through the proof space in the process.

Native Prolog-like Python implementation for RIF-Core, OWL 2, and SPARQL.  
"""

import itertools, copy, md5, pickle
from FuXi.Rete.AlphaNode import ReteToken, AlphaNode
from FuXi.Horn.HornRules import Clause, Ruleset, Rule, HornFromN3
from FuXi.Rete.RuleStore import *
from FuXi.Rete.Magic import AdornLiteral
from FuXi.Horn.PositiveConditions import *
from FuXi.Rete.Proof import *
from FuXi.Rete.Util import selective_memoize, lazyGeneratorPeek
from rdflib.Graph import ReadOnlyGraphAggregate
from rdflib import URIRef, RDF, Namespace, Variable
from rdflib.util import first
from rdflib.syntax.xml_names import split_uri
from FuXi.Rete.SidewaysInformationPassing import *
from FuXi.SPARQL import EDBQuery, normalizeBindingsAndQuery

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
    secondOrderRules = set()
    for rule in adornedRuleset:
        ruleHead = GetOp(rule.formula.head)
        if isinstance(ruleHead,Variable):
            #We store second order rules (i.e., rules whose head is a 
            #predicate occurrence whose predicate symbol is a variable) aside
            secondOrderRules.add(rule)
        headToRule.setdefault(ruleHead,set()).add(rule)
        graphs.append(rule.sip)
    #Second order rules are mapped from a None key (in order to indicate they are wildcards)
    headToRule[None]=secondOrderRules
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

def tripleToTriplePattern(graph,term):
    if isinstance(term,N3Builtin):
        template = graph.templateMap[term.uri]
        return "FILTER(%s)"%(template%(term.argument.n3(),
                                       term.result.n3()))
    else:
        return "%s %s %s"%tuple([renderTerm(graph,term) 
                                    for term in term.toRDFTuple()])
@selective_memoize([0])
def normalizeUri(rdfTerm,revNsMap):
    """
    Takes an RDF Term and 'normalizes' it into a QName (using the registered prefix)
    or (unlike compute_qname) the Notation 3 form for URIs: <...URI...> 
    """
    try:
        namespace, name = split_uri(rdfTerm)
        namespace = URIRef(namespace)
    except:
        if isinstance(rdfTerm,Variable):
            return "?%s"%rdfTerm
        else:
            return "<%s>"%rdfTerm
    prefix = revNsMap.get(namespace)
    if prefix is None and isinstance(rdfTerm,Variable):
        return "?%s"%rdfTerm
    elif prefix is None:
        return "<%s>"%rdfTerm
    else:
        qNameParts = compute_qname(rdfTerm,revNsMap)         
        return ':'.join([qNameParts[0],qNameParts[-1]])    

@selective_memoize([0])
def compute_qname(uri,revNsMap):
    namespace, name = split_uri(uri)
    namespace = URIRef(namespace)
    prefix = revNsMap.get(namespace)
    if prefix is None:
        prefix = "_%s" % len(revNsMap)
        revNsMap[namespace]=prefix
    return (prefix, namespace, name)

def renderTerm(graph,term):
    if term == RDF.type:
        return ' a '
    elif isinstance(term,URIRef):
        qname = normalizeUri(term,hasattr(graph,'revNsMap') and graph.revNsMap or \
                             dict([(u,p) for p,u in graph.namespaces()]))
        return qname[0] == '_' and u"<%s>"%term or qname
    else:
        try:
            return isinstance(term,BNode) and term.n3() or graph.qname(term)
        except:
            return term.n3()

def RDFTuplesToSPARQL(conjunct, 
                      edb, 
                      isGround=False, 
                      vars=[],
                      symmAtomicInclusion=False):
    """
    Takes a conjunction of Horn literals and returns the 
    corresponding SPARQL query 
    """
    queryType = isGround and "ASK" or "SELECT %s"%(' '.join([v.n3() 
                                                             for v in vars]))
    queryShell = len(conjunct)>1 and "%s {\n%s\n}" or "%s { %s }"
    if symmAtomicInclusion:
        if vars:
            var = vars.pop()
            prefix = "%s a ?KIND"%var.n3()
        else:
            
            prefix = "%s a ?KIND"%first([lit.arg[0].n3() for lit in conjunct])
        subquery = queryShell%(queryType,
                               "%s\nFILTER(%s)"%(
                             prefix,
                             ' ||\n'.join([
                               '?KIND = %s'%edb.qname(GetOp(lit)) 
                                    for lit in conjunct])))        
    else: 
        subquery = queryShell%(queryType,' .\n'.join(['\t'+tripleToTriplePattern(
                                                              edb,
                                                              lit) 
                                  for lit in conjunct ]))
    return subquery
    
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
            assert v == val2,"Failure merging %s to %s"%(mapping1,mapping2) 
            continue
        else: 
            newMap[k] = mapping1[k]
    newMap.update(mapping2)
    return makeImmutable and MakeImmutableDict(newMap) or newMap
         
class RuleFailure(Exception): 
    def __init__(self, msg):
        self.msg = msg
    def __repr__(self):
        return "RuleFailure: %"%self.msg 

class parameterizedPredicate:
    def __init__(self, externalVar):
        self.externalVar = externalVar
    def __call__(self, f):
        def _func(item):
            return f(item,self.externalVar)
        return _func

def invokeRule(priorAnswers,
               bodyLiteralIterator,
               sip,
               otherargs,
               priorBooleanGoalSuccess=False,
               step = None,
               debug = False,
               buildProof = False):
    """
    Continue invokation of rule using (given) prior answers and list of remaining
    body literals (& rule sip).  If prior answers is a list, computation is split 
    disjunctively
    
    [..] By combining the answers to all these subqueries, we generate
    answers for the original query involving the rule head
    
    Can also takes a PML step and updates it as it navigates the top-down proof
    tree (passing it on and updating it where necessary)

    """
    assert not buildProof or step is not None 
    proofLevel, memoizeMemory, sipCollection, factGraph, derivedPreds, processedRules = otherargs
    remainingBodyList = [i for i in bodyLiteralIterator]
    lazyGenerator = lazyGeneratorPeek(priorAnswers,2)
    if lazyGenerator.successful: 
        #There are multiple answers in this step, we need to call invokeRule
        #recursively for each answer, returning the first positive attempt
        success = False
        rt = None
        _step = None
        ansNo = 0
        for priorAns in lazyGenerator:
            ansNo += 1
            try:
                if buildProof:
                    newStep = InferenceStep(step.parent,
                                            step.rule,
                                            source=step.source)
                    newStep.antecedents = [ant for ant in step.antecedents]
                else:
                    newStep = None
                for rt,_step in\
                   invokeRule([priorAns],
                              iter([i for i in remainingBodyList]),
                              sip,
                              otherargs,
                              priorBooleanGoalSuccess,
                              newStep,
                              debug = debug,
                              buildProof = buildProof):
                    if rt:
                        yield rt,_step
            except RuleFailure, e: pass
        if not success:
            #None of prior answers were successful
            #indicate termination of rule processing
            raise RuleFailure(
              "Unable to solve either of %s against remainder of rule: %s"%(
                    ansNo,remainingBodyList))
#            yield False,_InferenceStep(step.parent,step.rule,source=step.source)
    else:
        lazyGenerator = lazyGeneratorPeek(lazyGenerator)
        projectedBindings = lazyGenerator.successful and first(lazyGenerator) or {}

        #First we check if we can combine a large group of subsequent body literals
        #into a single query        
        #if we have a template map then we use it to further
        #distinguish which builtins can be solved via 
        #cumulative SPARQl query - else we solve
        #builtins one at a time
        def sparqlResolvable(literal):
            if isinstance(literal,Uniterm):
                return not literal.naf and GetOp(literal) not in derivedPreds
            else:
                return isinstance(literal,N3Builtin) and \
                       literal.uri in factGraph.templateMap
        def sparqlResolvableNoTemplates(literal):
            if isinstance(literal,Uniterm):
                return not literal.naf and GetOp(literal) not in derivedPreds
            else:
                return False
                   
        conjGroundLiterals = list(itertools.takewhile(
                          hasattr(factGraph,'templateMap') and sparqlResolvable or \
                          sparqlResolvableNoTemplates,
                          remainingBodyList))
        bodyLiteralIterator = iter(remainingBodyList)
        if len(conjGroundLiterals)>1:
            #If there are literals to combine *and* a mapping from rule
            #builtins to SPARQL FILTER templates ..
            basePredicateVars = set(
                    reduce(lambda x,y:x+y,
                           map(lambda arg:list(GetVariables(arg,secondOrder=True)),
                               conjGroundLiterals)))
            if projectedBindings: 
                openVars = basePredicateVars.intersection(projectedBindings)
            else:
                #We don't have any given bindings, so we need to treat
                #the body as an open query
                openVars = basePredicateVars
            queryConj = EDBQuery([copy.deepcopy(lit) for lit in conjGroundLiterals],
                                    factGraph,
                                    openVars,
                                    projectedBindings)
            query,answers = queryConj.evaluate(debug)
            if isinstance(answers,bool):
                combinedAnswers = {}
                rtCheck = answers
            else:
                if projectedBindings:
                    combinedAnswers = (mergeMappings1To2(ans,
                                                         projectedBindings,
                                                         makeImmutable=True) for ans in answers )
                else:
                    combinedAnswers = ( MakeImmutableDict(ans) for ans in answers )
                combinedAnsLazyGenerator = lazyGeneratorPeek(combinedAnswers)
                rtCheck = combinedAnsLazyGenerator.successful
            if not rtCheck:
                raise RuleFailure("No answers for combined SPARQL query: %s"%query)
            else:
                #We have solved the previous N body literals with a single 
                #conjunctive query, now we need to make each of the literals
                #an antecedent to a 'query' step.
                if buildProof:
                    queryStep = InferenceStep(None,source='some RDF graph')
                    queryStep.groundQuery = subquery
                    queryStep.bindings = {}#combinedAnswers[-1]
                    queryHash = URIRef("tag:info@fuxi.googlecode.com:Queries#"+md5.new(
                                                subquery).hexdigest())
                    queryStep.identifier = queryHash
                    for subGoal in conjGroundLiterals:
                        subNs=NodeSet(subGoal.toRDFTuple(),
                                   identifier=BNode())
                        subNs.steps.append(queryStep)
                        step.antecedents.append(subNs)
                        queryStep.parent = subNs
                for rt,_step in invokeRule(
                               isinstance(answers,bool) and [projectedBindings] or combinedAnsLazyGenerator,
                               iter(remainingBodyList[len(conjGroundLiterals):]),
                               sip,
                               otherargs,
                               isinstance(answers,bool),
                               step,
                               debug = debug,
                               buildProof = buildProof):
                    yield rt,_step
            
                    
        else:
            #Continue processing rule body condition
            #one literal at a time
            try:
                bodyLiteral = bodyLiteralIterator.next()
                
                #if a N3 builtin, execute it using given bindings for boolean answer
                #builtins are moved to end of rule when evaluating rules via sip
                if isinstance(bodyLiteral,N3Builtin):
                    lhs = bodyLiteral.argument
                    rhs = bodyLiteral.result
                    lhs = isinstance(lhs,Variable) and projectedBindings[lhs] or lhs
                    rhs = isinstance(rhs,Variable) and projectedBindings[rhs] or rhs
                    assert lhs is not None and rhs is not None
                    if bodyLiteral.func(lhs,rhs):
                        if debug:
                            print >> sys.stderr, "Invoked %s(%s,%s) -> True"%(
                                             bodyLiteral.uri,
                                             lhs,
                                             rhs)
                        #positive answer means we can continue processing the rule body
                        if buildProof:
                             ns=NodeSet(bodyLiteral.toRDFTuple(),
                                        identifier=BNode())
                             step.antecedents.append(ns)
                        for rt,_step in invokeRule(
                                           [projectedBindings],
                                           bodyLiteralIterator,
                                           sip,
                                           otherargs,
                                           step,
                                           priorBooleanGoalSuccess,
                                           debug = debug,
                                           buildProof = buildProof):
                            yield rt,_step
                    else:
                        if debug:
                            print >> sys.stderr, "Successfully invoked %s(%s,%s) -> False"%(
                                             bodyLiteral.uri,
                                             lhs,
                                             rhs)                
                        raise RuleFailure("Failed builtin invokation %s(%s,%s)"%
                                          (bodyLiteral.uri,
                                           lhs,
                                           rhs))
                else:
                    #For every body literal, subqueries are generated according to the sip      
                    sipArcPred = URIRef(GetOp(bodyLiteral)+'_'+'_'.join(GetArgs(bodyLiteral)))
                    assert len(list(IncomingSIPArcs(sip,sipArcPred)))<2
                    subquery = copy.deepcopy(bodyLiteral)
                    subquery.ground(projectedBindings)
                    for N,x in IncomingSIPArcs(sip,sipArcPred):
                        #That is, each subquery contains values for the bound arguments
                        #that are passed through the sip arcs entering the node 
                        #corresponding to that literal
                        
                        #Create query out of body literal and apply sip-provided bindings
                        subquery = copy.deepcopy(bodyLiteral)
                        subquery.ground(projectedBindings)
                    if literalIsGround(subquery):
                        #subquery is ground, so there will only be boolean answers
                        #we return the conjunction of the answers for the current
                        #subquery
                        
                        answer = False
                        ns = None
                        
                        answers = first(
                                    itertools.dropwhile(
                                            lambda item:not item[0],
                                            SipStrategy(
                                                    subquery.toRDFTuple(),
                                                    sipCollection,
                                                    factGraph,
                                                    derivedPreds,
                                                    MakeImmutableDict(projectedBindings),
                                                    processedRules,
                                                    network = step is not None and \
                                                            step.parent.network or None,
                                                    debug = debug,
                                                    buildProof = buildProof,
                                                    memoizeMemory = memoizeMemory,
                                                    proofLevel = proofLevel)))
                        if answers:
                            answer,ns = answers
                        if not answer and not bodyLiteral.naf or \
                            (answer and bodyLiteral.naf):
                            #negative answer means the invokation of the rule fails
                            #either because we have a positive literal and there
                            #is no answer for the subgoal or the literal is 
                            #negative and there is an answer for the subgoal
                            raise RuleFailure("No solutions solving ground query %s"%subquery)
                        else:
                            if buildProof:
                                if not answer and bodyLiteral.naf:
                                    ns.naf = True
                                step.antecedents.append(ns)
                            #positive answer means we can continue processing the rule body
                            #either because we have a positive literal and answers
                            #for subgoal or a negative literal and no answers for the
                            #the goal
                            for rt,_step in invokeRule(
                                               [projectedBindings],
                                               bodyLiteralIterator,
                                               sip,
                                               otherargs,
                                               True,
                                               step,
                                               debug = debug):
                                yield rt,_step
                    else:
                        _answers = \
                                SipStrategy(subquery.toRDFTuple(),
                                            sipCollection,
                                            factGraph,
                                            derivedPreds,
                                            MakeImmutableDict(projectedBindings),
                                            processedRules,
                                            network = step is not None and \
                                                    step.parent.network or None,
                                            debug = debug,
                                            buildProof = buildProof,
                                            memoizeMemory = memoizeMemory,
                                            proofLevel = proofLevel)
                        #solve (non-ground) subgoal
                        def collectAnswers(_ans):
                            for ans,ns in _ans: 
                                if isinstance(ans,dict):
                                    try:
                                        map = mergeMappings1To2(ans,
                                                                projectedBindings,
                                                                makeImmutable=True)
                                        yield map
                                    except: pass
                        combinedAnswers = collectAnswers(_answers)
                        answers = lazyGeneratorPeek(combinedAnswers)
                        if not answers.successful and not bodyLiteral.naf or\
                          (bodyLiteral.naf and answers.successful):
                            raise RuleFailure("No solutions solving ground query %s"%subquery)
                        else:
                            #either we have a positive subgoal and answers
                            #or a negative subgoal and no answers
                            if buildProof:
                                if answers.successful:
                                    goals = set([g for a,g in answers])
                                    assert len(goals)==1
                                    step.antecedents.append(goals.pop())
                                else:
                                    newNs = NodeSet(
                                                bodyLiteral.toRDFTuple(),
                                                network=step.parent.network,
                                                identifier=BNode(),
                                                naf = True)
                                    step.antecedents.append(newNs)
                            for rt,_step in invokeRule(
                                               answers,
                                               bodyLiteralIterator,
                                               sip,
                                               otherargs,
                                               priorBooleanGoalSuccess,
                                               step,
                                               debug = debug,
                                               buildProof = buildProof):
                                yield rt,_step
            except StopIteration:
                #Finished processing rule
                if priorBooleanGoalSuccess:
                    yield projectedBindings and projectedBindings or True, step
                elif projectedBindings:
                    #Return the most recent (cumulative) answers and the given step
                    yield projectedBindings, step
                else:
                    raise RuleFailure("Finished processing rule unsuccessfully")
                
def refactorMapping(keyMapping,origMapping):
    """
    Takes a mapping from one mapping domain (D1)
    to another mapping domain (D2) as well as a mapping
    whose keys are in D1 and returns a new 
    """
    if keyMapping:
        refactoredMapping = {}
        for inKey,outKey in keyMapping.items(): 
            if inKey in origMapping:
                refactoredMapping[outKey]=origMapping[inKey]
        return refactoredMapping
    else:
        return origMapping
 
def prepMemiozedAns(ans):
    return isinstance(ans,dict) and MakeImmutableDict(ans) or ans
    

def SipStrategy(query,
                sipCollection,
                factGraph,
                derivedPreds,
                bindings={},
                processedRules = None,
                network = None,
                debug = False,
                buildProof = False,
                memoizeMemory = None,
                proofLevel = 1):
    """
    Accordingly, we define a sip-strategy for computing the answers to a query 
    expressed using a set of Datalog rules, and a set of sips, one for each 
    adornment of a rule head, as follows...
    
    Each evaluation uses memoization (via Python decorators) but also relies on well-formed 
    rewrites for using semi-naive bottom up method over large SPARQL data.
    
    """
    memoizeMemory = memoizeMemory and memoizeMemory or {}
    queryLiteral = BuildUnitermFromTuple(query)
    processedRules = processedRules and processedRules or set()
    if bindings:
        #There are bindings.  Apply them to the terms in the query
        queryLiteral.ground(bindings)
    
    if debug:
        print >> sys.stderr, "%sSolving"%('\t'*proofLevel), queryLiteral, bindings
    #Only consider ground triple pattern isomorphism with matching bindings
    goalRDFStatement = queryLiteral.toRDFTuple()

    if queryLiteral in memoizeMemory:
        if debug:
            print >> sys.stderr, "%sReturning previously calculated results for "%\
                        ('\t'*proofLevel), queryLiteral
        for answers in memoizeMemory[queryLiteral]:
            yield answers
    elif AlphaNode(goalRDFStatement).alphaNetworkHash(
                                      True,
                                      skolemTerms=bindings.values()) in\
        [AlphaNode(r.toRDFTuple()).alphaNetworkHash(True,
                                                    skolemTerms=bindings.values())
            for r in processedRules
                if AdornLiteral(goalRDFStatement).adornment == \
                   r.adornment]:
        if debug:
            print >> sys.stderr, "%s Goal already processed..."%\
                ('\t'*proofLevel)
    else: 
        isGround = literalIsGround(queryLiteral)
        if buildProof:
            ns=NodeSet(goalRDFStatement,network=network,identifier=BNode())    
        else:
            ns = None
        adornedProgram = factGraph.adornedProgram    
        queryPred = GetOp(queryLiteral)
        if sipCollection is None:
            rules = []
        else:
            #For every rule head matching the query, we invoke the rule, 
            #thus determining an adornment, and selecting a sip to follow            
            rules = sipCollection.headToRule.get(queryPred,set())
            if None in sipCollection.headToRule:
                #If there are second order rules, we add them
                #since they are a 'wildcard'
                rules.update(sipCollection.headToRule[None])

        #maintained list of rules that haven't been processed before and
        #match the query
        validRules = []
        
        #each subquery contains values for the bound arguments that are passed 
        #through the sip arcs entering the node corresponding to that literal. For
        #each subquery generated, there is a set of answers.
        answers = []
        
        variableMapping = {}
        
        #Some TBox queries can be 'joined' together into SPARQL queries against
        #'base' predicates via an RDF dataset
        #These atomic concept inclusion axioms can be evaluated together
        #using a disjunctive operator at the body of a horn clause
        #where each item is a query of the form uniPredicate(?X):
        #Or( uniPredicate1(?X1), uniPredicate2(?X), uniPredicate3(?X),..)
        #In this way massive, conjunctive joins can be 'mediated' 
        #between the stated facts and the top-down solver
        @parameterizedPredicate([i for i in derivedPreds])
        def IsAtomicInclusionAxiomRHS(rule,dPreds):
            """
            This is an atomic inclusion axiom with
            a variable (or bound) RHS:  uniPred(?ENTITY)
            """
            bodyList = list(iterCondition(rule.formula.body))
            body = first(bodyList)
            return GetOp(body) not in dPreds and \
                   len(bodyList) == 1 and \
                   body.op == RDF.type
        
        atomicInclusionAxioms = list(ifilter(IsAtomicInclusionAxiomRHS,rules))
        if atomicInclusionAxioms and len(atomicInclusionAxioms) > 1:
            if debug:
                print >> sys.stderr, "\tCombining atomic inclusion axioms: "
                pprint(atomicInclusionAxioms,sys.stderr)            
            if buildProof:
                factStep = InferenceStep(ns,source='some RDF graph')
                ns.steps.append(factStep)
                
            axioms = [rule.formula.body 
                      for rule in atomicInclusionAxioms]
     
            #attempt to exaustively apply any available substitutions
            #and determine if query if fully ground
            vars = [v for v in GetArgs(queryLiteral,
                                       secondOrder=True) 
                                             if isinstance(v,Variable)]
            openVars,axioms,_bindings  = \
                    normalizeBindingsAndQuery(vars,
                                              bindings,
                                              axioms)
            if openVars:
                mappings = {}
                #See if we need to do any variable mappings from the query literals
                #to the literals in the applicable rules
                query,rt = EDBQuery(axioms,
                                    factGraph,
                                    openVars,
                                    _bindings).evaluate(debug,
                                                        symmAtomicInclusion=True)
                if buildProof:
                    factStep.groundQuery = subquery
                for ans in rt:
                    if buildProof:
                        factStep.bindings.update(ans)
                    memoizeMemory.setdefault(queryLiteral,set()).add(
                                         (prepMemiozedAns(ans),ns))
                    yield ans, ns
            else:
                #All the relevant derivations have been explored and the result
                #is a ground query we can directly execute against the facts
                if buildProof:
                    factStep.bindings.update(bindings)
                query,rt = EDBQuery(axioms,
                                    factGraph,
                                    _bindings).evaluate(debug,
                                                        symmAtomicInclusion=True)                    
                if buildProof:
                    factStep.groundQuery = subquery
                memoizeMemory.setdefault(queryLiteral,set()).add(
                                         (prepMemiozedAns(rt),ns))                    
                yield rt,ns
            rules = ifilter(lambda i:not IsAtomicInclusionAxiomRHS(i),rules)                
        for rule in rules:
            #An exception is the special predicate ph; it is treated as a base 
            #predicate and the tuples in it are those supplied for qb by unification.
            headBindings = getBindingsFromLiteral(goalRDFStatement,rule.formula.head)
            comboBindings = dict([(k,v) for k,v in itertools.chain(
                                                      bindings.items(),
                                                      headBindings.items())])
            varMap = rule.formula.head.getVarMapping(queryLiteral)
            if headBindings and\
                [term for term in rule.formula.head.getDistinguishedVariables(True)
                        if varMap.get(term,term) not in headBindings]:
                continue
            subQueryAnswers = []
            dontStop = True
            projectedBindings = comboBindings.copy()
            if debug:
                print >> sys.stderr, "%sProcessing rule"%\
                ('\t'*proofLevel), rule.formula
                if debug and sipCollection:
                    print >>sys.stderr,"Sideways Information Passing (sip) graph for %s: "%queryLiteral
                    print >>sys.stdout, sipCollection.serialize(format='n3')
                    for sip in SIPRepresentation(sipCollection):
                        print >>sys.stderr,sip                
            try:
                #Invoke the rule
                if buildProof:
                    step = InferenceStep(ns,rule.formula)
                else:
                    step = None
                for rt,step in\
                  invokeRule([headBindings],
                              iter(iterCondition(rule.formula.body)),
                              rule.sip,
                              (proofLevel + 1,
                               memoizeMemory,
                               sipCollection, 
                               factGraph, 
                               derivedPreds,
                               processedRules.union([
                                 AdornLiteral(query)])),
                              step=step,
                              debug = debug):
                    if rt:
                        if isinstance(rt,dict):
                            #We received a mapping and must rewrite it via
                            #correlation between the variables in the rule head
                            #and the variables in the original query (after applying 
                            #bindings) 
                            varMap = rule.formula.head.getVarMapping(queryLiteral)
                            if varMap:
                                rt = MakeImmutableDict(refactorMapping(varMap,rt))
                            if buildProof:
                                step.bindings = rt
                        else:
                            if buildProof:
                                step.bindings = headBindings
                        validRules.append(rule)
                        if buildProof:
                            ns.steps.append(step)
                        if isGround:
                            yield True,ns
                        else:
                            memoizeMemory.setdefault(queryLiteral,set()).add(
                                                     (prepMemiozedAns(rt),
                                                      ns))        
                            yield rt, ns 
                
            except RuleFailure, e:
                #Clean up failed antecedents
                if buildProof:
                    if ns in step.antecedents:
                        step.antecedents.remove(ns)
        if not validRules:
            #No rules matching, query factGraph for answers
            successful = False
            if buildProof:
                factStep = InferenceStep(ns,source='some RDF graph')
                ns.steps.append(factStep)
            if not isGround:
                subquery,rt = EDBQuery([queryLiteral],
                                        factGraph,
                                        [v for v in GetArgs(queryLiteral,
                                                            secondOrder=True)
                                                                 if isinstance(v,Variable)],

                                        bindings).evaluate(debug)                    
                if buildProof:
                    factStep.groundQuery = subquery
                for ans in rt:
                    successful =True
                    if buildProof:
                        factStep.bindings.update(ans)
                    memoizeMemory.setdefault(queryLiteral,set()).add(
                                             (prepMemiozedAns(ans),
                                              ns))
                    yield ans, ns
                if not successful and queryPred not in derivedPreds:
                    #Open query didn't return any results and the predicate
                    #is ostensibly marked as derived predicate, so we have failed
                    memoizeMemory.setdefault(queryLiteral,set()).add((False,ns))
                    yield False,ns
            else:
                #All the relevant derivations have been explored and the result
                #is a ground query we can directly execute against the facts
                if buildProof:
                    factStep.bindings.update(bindings)

                subquery,rt = EDBQuery([queryLiteral],
                                        factGraph,
                                        bindings).evaluate(debug)                    
                if buildProof:
                    factStep.groundQuery = subquery
                memoizeMemory.setdefault(queryLiteral,set()).add(
                                             (prepMemiozedAns(rt),
                                              ns))                    
                yield rt,ns

def test():
     import doctest
     doctest.testmod()    
if __name__ == '__main__':
    test()