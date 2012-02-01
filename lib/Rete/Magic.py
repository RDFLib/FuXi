# -*- coding: utf-8 -*-
"""
[[[
    One method, called magic sets,is a general algorithm for rewriting logical rules
so that they may be implemented bottom-UP (= forward chaining) in a way that
is that by working bottom-up, we can take advantage of efficient methods for doing
massive joins.
]]] -- Magic Sets and Other Strange Ways to Implement Logic Programs, F. Bancilhon,
D. Maier, Y. Sagiv and J. Ullman, Proc. 5th ACM SIGMOD-SIGACT Symposium on
Principles of Database Systems, 1986.

" [..] proposed transformation is to define additional predicates that compute the values that 
are passed from one predicate to another in the original rules, according to the sip strategy chosen for each
rule. Each of the original rules is then modified so that it fires only when values for these
additional predicates are available. These auxiliary predicates are called "magic predicates" and
the sets of values that they compute are called "magic sets". The intention is that the bottom-up
evaluation of the modified set of rules simulate the sip we have chosen for each adorned rule,
thus restricting the search space."

" we are interested in binding propagation and how it can be used to improve the
 efficiency of evaluation in the presence of recursion

"""
import unittest, itertools, copy

import unittest, os, time, itertools, copy
from FuXi.Rete.RuleStore import SetupRuleStore, N3RuleStore, N3Builtin, LOG
from FuXi.Rete.AlphaNode import ReteToken
from FuXi.Rete.BetaNode import project
from FuXi.Horn.HornRules import Clause, Ruleset, Rule
from FuXi.DLP.ConditionalAxioms import AdditionalRules
from FuXi.Syntax.InfixOWL import OWL_NS

from FuXi.Horn.PositiveConditions import *
from FuXi.Rete.Proof import *
from FuXi.Syntax.InfixOWL import OWL_NS
from cStringIO import StringIO
from rdflib import URIRef, RDF, RDFS, Namespace, Variable, Literal
from rdflib.util import first
try:
    from rdflib.collection import Collection
    from rdflib.graph import Graph, ReadOnlyGraphAggregate
    from rdfextras.sparql.algebra import RenderSPARQLAlgebra
    from rdfextras.sparql.parser import parse
except ImportError:
    from rdflib.Collection import Collection
    from rdflib.Graph import Graph, ReadOnlyGraphAggregate
    from rdflib.sparql.Algebra import RenderSPARQLAlgebra
    from rdflib.sparql.parser import parse
from FuXi.Rete.SidewaysInformationPassing import *

EX_ULMAN = Namespace('http://doi.acm.org/10.1145/6012.15399#')
LOG_NS   = Namespace("http://www.w3.org/2000/10/swap/log#")
MAGIC = Namespace('http://doi.acm.org/10.1145/28659.28689#')

DDL_STRICTNESS_LOOSE    = 0
DDL_STRICTNESS_HARSH    = 1
DDL_STRICTNESS_FALLBACK_DERIVED = 2
DDL_STRICTNESS_FALLBACK_BASE = 3 
DDL_MUST_CHECK = [DDL_STRICTNESS_HARSH,
                  DDL_STRICTNESS_FALLBACK_DERIVED,
                  DDL_STRICTNESS_FALLBACK_BASE]
DDL_FALLBACK = [
    DDL_STRICTNESS_FALLBACK_DERIVED,
    DDL_STRICTNESS_FALLBACK_BASE
]

nameMap = {
  'loose'          : DDL_STRICTNESS_LOOSE,
  'defaultDerived' : DDL_STRICTNESS_FALLBACK_DERIVED,
  'defaultBase'    : DDL_STRICTNESS_FALLBACK_BASE,
  'harsh'          : DDL_STRICTNESS_HARSH,
}

def SetupDDLAndAdornProgram(factGraph,
                            rules,
                            GOALS,
                            derivedPreds=None,
                            strictCheck=DDL_STRICTNESS_FALLBACK_DERIVED,
                            defaultPredicates=None,
                            ignoreUnboundDPreds=False,
                            hybridPreds2Replace=None):
    if not defaultPredicates:
        defaultPredicates = [],[]
    # _dPredsProvided = bool(derivedPreds)
    if not derivedPreds:
        _derivedPreds=DerivedPredicateIterator(factGraph,
                                               rules,
                                               strict=strictCheck,
                                               defaultPredicates=defaultPredicates)
        if not isinstance(derivedPreds,(set,list)):
            derivedPreds=list(_derivedPreds)
        else:
            derivedPreds.extend(_derivedPreds)
    hybridPreds2Replace = hybridPreds2Replace or []
    adornedProgram = AdornProgram(
                        factGraph,
                        rules,
                        GOALS,
                        derivedPreds,
                        ignoreUnboundDPreds,
                        hybridPreds2Replace = hybridPreds2Replace)
    rt=reduce(lambda l,r: l+r,
              [list(iterCondition(clause.formula.body))
                    for clause in adornedProgram])
    for hybridPred, adornment in [(t,a)
        for t,a in set(
            [ (URIRef(GetOp(term).split('_derived')[0]
                   ) if GetOp(term).find('_derived')+1 else GetOp(term),
               ''.join(term.adornment)
               ) for term in rt if isinstance(term,AdornedUniTerm)])
            if t in hybridPreds2Replace]:
        #If there are hybrid predicates, add rules that derived their IDB counterpart
        #using information from the adorned queries to determine appropriate arity
        #and adornment
        hybridPred      = URIRef(hybridPred)
        hPred           = URIRef(hybridPred + u'_derived')
        if len(adornment) == 1:
            # p_derived^{a}(X) :- p(X)
            body = BuildUnitermFromTuple(
                                (Variable('X'),
                                 RDF.type,
                                 hybridPred))
            head = BuildUnitermFromTuple(
                                (Variable('X'),
                                 RDF.type,
                                 hPred))
        else:
            # p_derived^{a}(X,Y) :- p(X,Y)
            body = BuildUnitermFromTuple(
                                (Variable('X'),
                                 hybridPred,
                                 Variable('Y')))
            head = BuildUnitermFromTuple(
                                (Variable('X'),
                                 hPred,
                                 Variable('Y')))
        _head=AdornedUniTerm(head,list(adornment))
        rule=AdornedRule(Clause(And([body]),_head.clone()))
        rule.sip = Graph()
        adornedProgram.add(rule)

    if factGraph is not None:
        factGraph.adornedProgram = adornedProgram    
    return adornedProgram

def MagicSetTransformation(factGraph,
                           rules,
                           GOALS,
                           derivedPreds=None,
                           strictCheck=DDL_STRICTNESS_FALLBACK_DERIVED,
                           noMagic=None,
                           defaultPredicates=None):
    """
    Takes a goal and a ruleset and returns an iterator
    over the rulest that corresponds to the magic set
    transformation:
    """
    noMagic = noMagic and noMagic or []
    magicPredicates=set()
    # replacement={}
    adornedProgram = SetupDDLAndAdornProgram(
                                   factGraph,
                                   rules,
                                   GOALS,
                                   derivedPreds=derivedPreds,
                                   strictCheck=strictCheck,
                                   defaultPredicates=defaultPredicates)
    newRules=[]
    for rule in adornedProgram: 
        if rule.isSecondOrder():
            import warnings
            warnings.warn(
            "Second order rule no supported by GMS: %s"%rule,
                    RuntimeWarning)
            
        magicPositions={}
        #Generate magic rules
        for idx,pred in enumerate(iterCondition(rule.formula.body)):
            # magicBody=[]
            if isinstance(pred,AdornedUniTerm):# and pred not in magicPredicates:
                # For each rule r in Pad, and for each occurrence of an adorned 
                # predicate p a in its body, we generate a magic rule defining magic_p a
                prevPreds=[item for _idx,item in enumerate(rule.formula.body)
                                            if _idx < idx]             
                if 'b' not in pred.adornment:
                    import warnings
                    warnings.warn(
"adorned predicate w/out any bound arguments(%s in %s) !"%(pred,rule.formula),
                            RuntimeWarning)
                if GetOp(pred) not in noMagic:
                    magicPred=pred.makeMagicPred()
                    magicPositions[idx]=(magicPred,pred)
                    inArcs=[(N,x) for (N,x) in IncomingSIPArcs(rule.sip,getOccurrenceId(pred))
                                        if not set(x).difference(GetArgs(pred))]
                    if len(inArcs) > 1:
    #                    If there are several arcs entering qi, we define the magic rule defining magic_qi
    #                    in two steps. First, for each arc Nj --> qi with label cj , we define a rule with head label_qi_j(cj ). The body
    #                    of the rule is the same as the body of the magic rule in the case where there is a single arc
    #                    entering qi (described above). Then the magic rule is defined as follows. The head is
    #                    magic_q(0). The body contains label_qi_j(cj) for all j (that is, for all arcs entering qi ).
    
                        #We combine all incoming arcs into a single list of (body) conditions for the magic set
                        PrettyPrintRule(rule)
                        SIPRepresentation(rule.sip)
                        print pred, magicPred
                        _body=[]
                        additionalRules=[]
                        for idxSip,(N,x) in enumerate(inArcs):
                            newPred=pred.clone()
                            SetOp(newPred,URIRef('%s_label_%s'%(newPred.op,idxSip)))
                            ruleBody=And(buildMagicBody(
                                    N,
                                    prevPreds,
                                    rule.formula.head,
                                    derivedPreds))
                            additionalRules.append(Rule(Clause(ruleBody,newPred)))
                            _body.extend(newPred)                        
    #                        _body.extend(ruleBody)
                        additionalRules.append(Rule(Clause(And(_body),magicPred)))
                        newRules.extend(additionalRules)
                        for i in additionalRules:
                            print i
                        raise NotImplementedError()
                    else:
                        for idxSip,(N,x) in enumerate(inArcs):
                            ruleBody=And(buildMagicBody(
                                    N,
                                    prevPreds,
                                    rule.formula.head,
                                    derivedPreds,
                                    noMagic))
                            newRule=Rule(Clause(ruleBody,magicPred))
                            newRules.append(newRule)
                    magicPredicates.add(magicPred)
        #Modify rules
        #we modify the original rule by inserting
        #occurrences of the magic predicates corresponding
        #to the derived predicates of the body and to the head
        #If there are no bound arguments in the head, we don't modify the rule
        idxIncrement=0
        newRule=copy.deepcopy(rule)
        for idx,(magicPred,origPred) in magicPositions.items():
            newRule.formula.body.formulae.insert(idx+idxIncrement,magicPred)
            idxIncrement+=1
        if 'b' in rule.formula.head.adornment and GetOp(rule.formula.head) not in noMagic:
            headMagicPred=rule.formula.head.makeMagicPred()
            if isinstance(newRule.formula.body,Uniterm):
                newRule.formula.body = And([headMagicPred,newRule.formula.body])
            else:
                newRule.formula.body.formulae.insert(0,headMagicPred)
        newRules.append(newRule)

    if not newRules:
        newRules.extend(AdditionalRules(factGraph))
    for rule in newRules:
        if rule.formula.body:
            yield rule
        
def NormalizeGoals(goals):
    if isinstance(goals,(list,set)):
        for goal in goals:
            yield goal,{}
    elif isinstance(goals,tuple):
        yield sparqlQuery,{}
    else:
        query=RenderSPARQLAlgebra(parse(goals))
        for pattern in query.patterns:
            yield pattern[:3],query.prolog.prefixBindings
    
class AdornedRule(Rule):
    """Rule with 'bf' adornment and is comparable"""
    def __init__(self, clause, declare=None,nsMapping=None):
        decl=set()
        self.ruleStr=''
        for pred in itertools.chain(iterCondition(clause.head),
                                    iterCondition(clause.body)):
            decl.update([term for term in GetArgs(pred) if isinstance(term,Variable)])
            if isinstance(pred,AdornedUniTerm):
                self.ruleStr+=''.join(pred.adornment)
            self.ruleStr+=''.join(pred.toRDFTuple())
        super(AdornedRule, self).__init__(clause,decl,nsMapping)        

    def isRecursive(self):
        def termHash(term):
            return GetOp(term),\
                   reduce(lambda x,y:x+y,term.adornment)
        headHash = termHash(self.formula.head)
        def recursiveLiteral(term):
            return isinstance(term,AdornedUniTerm) and termHash(term) == headHash        
        if first(itertools.ifilter(recursiveLiteral,iterCondition(self.formula.body))):
            return True
        else:
            return False

    def __hash__(self):
        return hash(self.ruleStr)
        
    def __eq__(self,other):
        return hash(self) == hash(other)   

def NormalizeUniterm(term):
    if isinstance(term,Uniterm):
        return term
    elif isinstance(term,N3Builtin):
        return Uniterm(term.uri,term.argument,term.naf) 
    
def AdornRule(derivedPreds,
              clause,
              newHead,
              ignoreUnboundDPreds = False,
              hybridPreds2Replace = None):
    """
    Adorns a horn clause using the given new head and list of
    derived predicates
    """
    assert len(list(iterCondition(clause.head)))==1
    hybridPreds2Replace = hybridPreds2Replace or []
    adornedHead=AdornedUniTerm(clause.head,
                               newHead.adornment)
    sip=BuildNaturalSIP(clause,
                        derivedPreds,
                        adornedHead,
                        hybridPreds2Replace=hybridPreds2Replace,
                        ignoreUnboundDPreds=ignoreUnboundDPreds)
    bodyPredReplace={}
    def adornment(arg,headArc,x):
        if headArc:
            #Sip arc from head
            #don't mark bound if query has no bound/distinguished terms
            return (arg in x and 
                    arg in adornedHead.getDistinguishedVariables(True)) \
                        and 'b' or 'f'
        else:
            return arg in x and 'b' or 'f'
    for literal in iterCondition(sip.sipOrder):
        op   = GetOp(literal)
        args = GetArgs(literal)
        if op in derivedPreds or (op in hybridPreds2Replace if hybridPreds2Replace else False):
            for N,x in IncomingSIPArcs(sip,getOccurrenceId(literal)): 
                headArc = len(N)==1 and N[0] == GetOp(newHead)                
                if not set(x).difference(args):
                    # A binding
                    # for q is useful, however, only if it is a binding for an argument of q.
                    bodyPredReplace[literal]=AdornedUniTerm(NormalizeUniterm(literal),
                            [ adornment(arg,headArc,x) for arg in args],literal.naf)
#                For a predicate occurrence with no incoming
#                arc, the adornment contains only f. For our purposes here, 
#                we do not distinguish between a predicate with such an 
#                adornment and an unadorned predicate (we do in order to support open queries)
            if literal not in bodyPredReplace and ignoreUnboundDPreds:
                bodyPredReplace[literal]=AdornedUniTerm(NormalizeUniterm(literal),
                        [ 'f' for arg in GetArgs(literal)],literal.naf)
    if hybridPreds2Replace:
        atomPred = GetOp(adornedHead)
        if atomPred in hybridPreds2Replace:
            adornedHead.setOperator(URIRef(atomPred + u'_derived'))
        for bodAtom in [bodyPredReplace.get(p,p)
                                for p in iterCondition(sip.sipOrder)]:
            bodyPred = GetOp(bodAtom)
            if bodyPred in hybridPreds2Replace:
                bodAtom.setOperator(URIRef(bodyPred + u'_derived'))
    rule=AdornedRule(Clause(And([bodyPredReplace.get(p,p)
                                for p in iterCondition(sip.sipOrder)]),
                            adornedHead))
    rule.sip = sip
    return rule

def BasePredicateFromHybrid(pred):
    return URIRef(pred[:-8])

def IsHybridPredicate(pred,hybridPreds2Replace):
    op = GetOp(pred)
    return op[-7:] == 'derived' and op[:-8] in hybridPreds2Replace

def compareAdornedPredToRuleHead(aPred,head, hybridPreds2Replace):
    """
    If p_a is an unmarked adorned predicate, then for each rule that has p in its head, ..
    """
    headPredicateTerm = GetOp(head)
    aPredTerm         = GetOp(aPred)
    assert isinstance(head,Uniterm)
    if head.getArity() == aPred.getArity():
        return headPredicateTerm == aPredTerm or isinstance(headPredicateTerm,
                                                            Variable) or (
               IsHybridPredicate(aPred,hybridPreds2Replace) and 
               aPredTerm[:-8] == headPredicateTerm)
    return False

def AdornProgram(factGraph,
                 rs,
                 goals,
                 derivedPreds=None,
                 ignoreUnboundDPreds=False,
                 hybridPreds2Replace=None):
    """
    The process starts from the given query. The query determines bindings for q, and we replace
    q by an adorned version, in which precisely the positions bound in the query are designated as
    bound, say q e . In general, we have a collection of adorned predicates, and as each one is processed,
    we will mark it, so that it will not be processed again. If p a is an unmarked adorned
    predicate, then for each rule that has p in its head, we generate an adorned version for the rule
    and add it to Pad; then p is marked as processed.    
    
    The adorned version of a rule contains additional
    adorned predicates, and these are added to the collection, unless they already appear
    there. The process terminates when no unmarked adorned predicates are left.
        
    """
    from FuXi.DLP import LloydToporTransformation
    from collections import deque
    goalDict = {}
    hybridPreds2Replace = hybridPreds2Replace or []
    adornedPredicateCollection=set()
    for goal,nsBindings in NormalizeGoals(goals):
        adornedPredicateCollection.add(AdornLiteral(goal,nsBindings))
    if not derivedPreds:
        derivedPreds=list(DerivedPredicateIterator(factGraph,rs))
    def unprocessedPreds(aPredCol):
        rt=[]
        for p in aPredCol:
            if not  p.marked:
                rt.append(p)
            if p not in goalDict:
                goalDict.setdefault(GetOp(p),set()).add(p)
        return rt
    toDo = deque(unprocessedPreds(adornedPredicateCollection))
    adornedProgram=set()
    while len(toDo):
        term = toDo.popleft()
        #check if there is a rule with term as its head
        for rule in rs:
            for clause in LloydToporTransformation(rule.formula):
                head=isinstance(clause.head,Exists) and clause.head.formula or clause.head
                # headPredicate = GetOp(head)
                if compareAdornedPredToRuleHead(term,head,hybridPreds2Replace):
                    #for each rule that has p in its head, we generate an adorned version for the rule
                    adornedRule=AdornRule(derivedPreds,
                                          clause,
                                          term,
                                          ignoreUnboundDPreds=ignoreUnboundDPreds,
                                          hybridPreds2Replace = hybridPreds2Replace)
                    adornedProgram.add(adornedRule)
                    #The adorned version of a rule contains additional adorned
                    #predicates, and these are added
                    for pred in iterCondition(adornedRule.formula.body):
                        if isinstance(pred,N3Builtin):
                            aPred = pred
                        else:
                            aPred = not isinstance(pred,AdornedUniTerm) and \
                                        AdornLiteral(pred.toRDFTuple(),
                                                     nsBindings,
                                                     pred.naf) or pred
                        op = GetOp(pred)
                        if (op in derivedPreds or
                            (op in hybridPreds2Replace if hybridPreds2Replace
                            else False)
                            ) and aPred not in adornedPredicateCollection:
                            adornedPredicateCollection.add(aPred)
        term.marked=True
        toDo.extendleft(unprocessedPreds(adornedPredicateCollection))
        
    factGraph.queryAtoms = goalDict
    return adornedProgram

class AdornedUniTerm(Uniterm):
    def __init__(self,uterm,adornment=None,naf = False):
        self.marked = False
        self.adornment=adornment
        self.nsMgr=GetUterm(uterm).nsMgr
        newArgs=copy.deepcopy(GetUterm(uterm).arg)
        super(AdornedUniTerm, self).__init__(GetUterm(uterm).op,newArgs,naf=naf)
        self.isMagic=False

    def clone(self):
        return AdornedUniTerm(self,self.adornment,self.naf)
                
    def makeMagicPred(self):
        """
        Make a (cloned) magic predicate
        
        The arity of the new predicate is the number of occurrences of b in the 
        adornment a, and its arguments correspond to the bound arguments of p a
        """
        newAdornedPred=AdornedUniTerm(self,self.adornment,self.naf)
        if self.op == RDF.type:
            newAdornedPred.arg[-1] = URIRef(self.arg[-1]+'_magic')
        elif len([i for i in self.adornment if i =='b'])==1:
            #adorned predicate occurrence with one out of two arguments bound
            #converted into a magic predicate: It becomes a unary predicate 
            #(an rdf:type assertion)
            newAdornedPred.arg[-1] = URIRef(self.op+'_magic')
            newAdornedPred.arg[0] = [self.arg[idx] 
                                        for idx,i in enumerate(self.adornment) 
                                                if i =='b'][0]            
            newAdornedPred.op = RDF.type
        else:
            newAdornedPred.op=URIRef(self.op+'_magic')
        newAdornedPred.isMagic=True
        return newAdornedPred

    def __hash__(self):
        return self._hash ^ hash(reduce(lambda x,y:x+y,self.adornment))
        
    # def __eq__(self,other):
    #     return self.adornment==other.adornment and\
    #            self.op==other.op and\
    #            self.arg==other.arg
                
    def hasBindings(self):
        for idx,term in enumerate(GetArgs(self)):
            if self.adornment[idx]=='b':
                if not varsOnly or isinstance(term,Variable):
                    return True
        return False
                
    def getDistinguishedVariables(self,varsOnly=False):
        if self.op == RDF.type:
            for idx,term in enumerate(GetArgs(self)):
                if self.adornment[idx]=='b':
                    if not varsOnly or isinstance(term,Variable):
                        yield term
        else:
            for idx,term in enumerate(self.arg):
                try:
                    if self.adornment[idx]=='b':
                        if not varsOnly or isinstance(term,Variable):
                            yield term
                except IndexError: pass
                  
    def getBindings(self,uniterm):
        rt={}
        for idx,term in enumerate(self.arg):
            goalArg=self.arg[idx]
            candidateArg=uniterm.arg[idx]
            if self.adornment[idx]=='b' and isinstance(candidateArg,Variable):
                #binding
                rt[candidateArg]=goalArg
        return rt
        
    def toRDFTuple(self):
        if hasattr(self,'isMagic') and self.isMagic:
            return (self.arg[0],self.op,self.arg[-1])
        else:
            subject,_object = self.arg
            return (subject,self.op,_object)
                
    def __repr__(self):
        pred = self.normalizeTerm(self.op)
        negPrefix = self.naf and 'not ' or ''
        if self.op == RDF.type:
            adornSuffix = '_'+self.adornment[0]
        else:
            adornSuffix='_'+''.join(self.adornment)
        if self.isMagic:
            if self.op == RDF.type:
                return "%s%s(%s)"%(negPrefix,
                                   self.normalizeTerm(self.arg[-1]),
                                   self.normalizeTerm(self.arg[0]))
            else:
                return "%s%s(%s)"%(negPrefix,
                                   pred,
                                ' '.join([self.normalizeTerm(i) 
                                            for idx,i in enumerate(self.arg) 
                                                    if self.adornment[idx]=='b']))
        elif self.op == RDF.type:
            return "%s%s%s(%s)"%(negPrefix,
                                 self.normalizeTerm(self.arg[-1]),
                                 adornSuffix,
                                 self.normalizeTerm(self.arg[0]))
        else:
            return "%s%s%s(%s)"%(negPrefix,
                                 pred,
                                 adornSuffix,
                                 ' '.join([self.normalizeTerm(i) 
                                            for i in self.arg]))

def AdornLiteral(rdfTuple,newNss=None,naf = False):
    """
    An adornment for an n-ary predicate p is a string a of length n on the 
    alphabet {b, f}, where b stands for bound and f stands for free. We 
    assume a fixed order of the arguments of the predicate.
    
    Intuitively, an adorned occurrence of the predicate, p a, corresponds to a 
    computation of the predicate with some arguments bound to constants, and 
    the other arguments free, where the bound arguments are those that are
    so indicated by the adornment.    
    
    >>> EX=Namespace('http://doi.acm.org/10.1145/6012.15399#')
    >>> query=RenderSPARQLAlgebra(parse(NON_LINEAR_MS_QUERY))
    >>> literal=query.patterns[0][:3]
    >>> literal
    (rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john'), rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#sg'), ?X)
    >>> aLit=AdornLiteral(literal,query.prolog.prefixBindings)
    >>> aLit
    mst:sg_bf(mst:john ?X)
    >>> aLit.adornment
    ['b', 'f']
    >>> aLit.getBindings(Uniterm(EX.sg,[Variable('X'),EX.jill]))
    {?X: rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john')}
    """
    args=[rdfTuple[0],rdfTuple[-1]]
    newNss=newNss is None and {} or newNss
    uTerm = BuildUnitermFromTuple(rdfTuple,newNss)
    opArgs=rdfTuple[1] == RDF.type and [args[0]] or args
    def isFreeTerm(term):
        return isinstance(term,Variable)
    adornment=[ isFreeTerm(term) and 'f' or 'b' for idx,term in enumerate(opArgs) ]
    return AdornedUniTerm(uTerm,adornment,naf)  

def DerivedPredicateIterator(factsOrBasePreds,
                             ruleset,
                             strict=DDL_STRICTNESS_FALLBACK_DERIVED,
                             defaultPredicates=None):
    if not defaultPredicates:
        defaultPredicates = [],[]
    defaultBasePreds,defaultDerivedPreds = defaultPredicates
    basePreds=[GetOp(buildUniTerm(fact)) for fact in factsOrBasePreds 
                        if fact[1] != LOG.implies]     
    processed={True:set(),False:set()}
    derivedPreds=set()
    uncertainPreds=set()
    ruleBodyPreds=set()
    ruleHeads=set()
    for rule in ruleset:
        if rule.formula.body:
            for idx,term in enumerate(itertools.chain(iterCondition(rule.formula.head),
                                      iterCondition(rule.formula.body))):
                #iterate over terms from head to end of body
                op = GetOp(term)
                if op not in processed[idx>0]: 
                    #not processed before
                    if idx > 0:
                        #body literal
                        ruleBodyPreds.add(op)
                    else:
                        #head literal
                        ruleHeads.add(op)
                    if strict in DDL_MUST_CHECK and \
                        not (op not in basePreds or idx > 0):
                        #checking DDL well formedness and
                        #op is a base predicate *and* a head literal (derived)
                        if strict in DDL_FALLBACK:
                            mark = strict == DDL_STRICTNESS_FALLBACK_DERIVED and \
                            'derived' or 'base'
                            if strict == DDL_STRICTNESS_FALLBACK_DERIVED and \
                                op not in defaultBasePreds:     
                                #a clashing predicate is marked as derived due
                                #to level of strictness                        
                                derivedPreds.add(op)
                            elif strict == DDL_STRICTNESS_FALLBACK_BASE and \
                                op not in defaultDerivedPreds:
                                #a clashing predicate is marked as base dur
                                #to level of strictness
                                defaultBasePreds.append(op)
                            import warnings
                            warnings.warn(
      "predicate symbol of %s is in both IDB and EDB. Marking as %s"%(term,mark))
                        else:
                            raise SyntaxError("%s is a member of a derived predicate and a base predicate!"%term)
                    if op in basePreds:
                        #base predicates are marked for later validation
                        uncertainPreds.add(op)
                    else:
                        if idx == 0 and not isinstance(op,Variable):
                            #head literal with proper predicate symbol
                            #identify as a derived predicate
                            derivedPreds.add(op)
                        elif not isinstance(op,Variable):
                            #body literal with proper predicate symbol
                            #mark for later validation
                            uncertainPreds.add(op)
                    processed[idx>0].add(op)
    for pred in uncertainPreds:
        #for each predicate marked as 'uncertain'
        #do further checking
        if (pred not in ruleBodyPreds and not isinstance(pred,Variable)) or\
           pred in ruleHeads:
            #pred is not in a body literal and is a proper predicate symbol
            #or it is a rule head -> mark as a derived predicate
            derivedPreds.add(pred)
    for pred in derivedPreds:
        if not pred in defaultBasePreds:
            yield pred
    
def iter_non_base_non_derived_preds(ruleset,intensional_db):
    rt=set()
    intensional_preds=set([p for p in intensional_db.predicates() 
                                    if p != LOG_NS.implies])
    for rule in ruleset:
        for uterm in rule.formula.head:
            if uterm.op in intensional_preds and uterm.op not in rt:
                rt.add(uterm.op)
                yield uterm.op, (fact 
                         for fact in intensional_db.triples((None,uterm.op,None)))

def buildMagicBody(N,prevPredicates,adornedHead,derivedPreds,noMagic=[]):
    unboundHead='b' in adornedHead.adornment
    if unboundHead:
        body=[adornedHead.makeMagicPred()]
    else:
        #If there are no bound argument positions to pass magic values with,
        #we propagate values in the full relation
        body=[]
    for prevAPred in prevPredicates:
        op = GetOp(prevAPred)
        if op in N or isinstance(op,Variable):
            #If qj, j<i, is in N, we add qj to the body of the magic rule
            #Note, if the atom has a variable for the predicate, treat it as a base
            #predicate occurrence
            body.append(prevAPred)
        if op in derivedPreds and isinstance(prevAPred,AdornedUniTerm) and prevAPred.adornment.count('b')>0:
            #If qj is a derived predicate and its adornment contains at least 
            #one b, we also add the corresponding magic predicate to the body
            if op in noMagic:
                body.append(prevAPred)
            else:
                body.append(prevAPred.makeMagicPred())
    return body

def PrettyPrintRule(rule):
    if isinstance(rule.formula.body,And):
        print rule.formula.head
        print "    :- %s"%rule.formula.body.formulae[0]
        for idx,literal in enumerate(rule.formula.body.formulae[1:]):
            print "       %s%s"%(literal,
                                 literal == rule.formula.body.formulae[-1] and '' or ', ')
    else:
        print rule.formula

OWL_PROPERTIES_QUERY=\
"""
SELECT ?prop
WHERE {
    ?prop a ?propType 
      FILTER( 
        ?propType = owl:ObjectProperty || 
        ?propType = owl:TransitiveProperty ||
        ?propType = owl:SymmetricProperty ||
        ?propType = owl:InverseFunctionalProperty ||
        ?propType = owl:DatatypeProperty )  
}"""

EXCLUDED_DERIVED_PREDS=\
[
    
]


def IdentifyDerivedPredicates(ddlMetaGraph,tBox,ruleset=None):
    """
    See: http://code.google.com/p/fuxi/wiki/DataDescriptionLanguage#
    """
    dPreds = set()
    basePreds = set()
    DDL = Namespace('http://code.google.com/p/fuxi/wiki/DataDescriptionLanguage#')
    
    if ruleset:
        for rule in ruleset:
            dPreds.add(GetOp(rule.formula.head))
    
    for derivedClassList in ddlMetaGraph.subjects(predicate=RDF.type,
                                          object=DDL.DerivedClassList):
        dPreds.update(Collection(ddlMetaGraph,derivedClassList))
    for derivedClassList in ddlMetaGraph.subjects(predicate=RDF.type,
                                          object=DDL.DerivedPropertyList):
        dPreds.update(Collection(ddlMetaGraph,derivedClassList))        
    derivedPropPrefixes = []
    basePropPrefixes    = []
    for derivedPropPrefixList in ddlMetaGraph.subjects(predicate=RDF.type,
                                               object=DDL.DerivedPropertyPrefix):
        derivedPropPrefixes.extend(Collection(ddlMetaGraph,derivedPropPrefixList))
    for basePropPrefixList in ddlMetaGraph.subjects(predicate=RDF.type,
                                               object=DDL.BasePropertyPrefix):
        basePropPrefixes.extend(Collection(ddlMetaGraph,basePropPrefixList))
        
    for prop in tBox.query(OWL_PROPERTIES_QUERY):
        if first(itertools.ifilter(lambda prefix:prop.startswith(prefix),
                                   derivedPropPrefixes)) and \
                       (prop,RDF.type,OWL_NS.AnnotationProperty) not in tBox: 
            dPreds.add(prop)
        if first(itertools.ifilter(lambda prefix:prop.startswith(prefix),
                                   basePropPrefixes)) and \
                       (prop,RDF.type,OWL_NS.AnnotationProperty) not in tBox and \
                       prop not in dPreds: 
            basePreds.add(prop)
            
    derivedClassPrefixes = []
    for derivedClsPrefixList in ddlMetaGraph.subjects(predicate=RDF.type,
                                              object=DDL.DerivedClassPrefix):
        derivedClassPrefixes.extend(Collection(ddlMetaGraph,
                                               derivedClsPrefixList))
    baseClassPrefixes = []
    for baseClsPrefixList in ddlMetaGraph.subjects(predicate=RDF.type,
                                             object=DDL.BaseClassPrefix):
       baseClassPrefixes.extend(Collection(ddlMetaGraph,
                                           baseClsPrefixList))
    for cls in tBox.subjects(predicate=RDF.type,
                             object=OWL_NS.Class):
        if first(itertools.ifilter(lambda prefix:cls.startswith(prefix),
                                   baseClassPrefixes)):
            if cls not in dPreds: 
                basePreds.add(cls)
        if first(itertools.ifilter(lambda prefix:cls.startswith(prefix),
                                   derivedClassPrefixes)):
            if cls not in basePreds: 
                dPreds.add(cls)
            
    nsBindings = dict([(prefix,nsUri) 
                       for prefix, nsUri in itertools.chain(
                               tBox.namespaces(),
                               ddlMetaGraph.namespaces())
                        if prefix])            
    for queryNode in ddlMetaGraph.subjects(predicate=RDF.type,
                                   object=DDL.DerivedClassQuery):
        query = first(ddlMetaGraph.objects(queryNode,RDF.value))
        for cls in tBox.query(query,
                              initNs=nsBindings):
            dPreds.add(cls)
            
    for baseClsList in ddlMetaGraph.subjects(predicate=RDF.type,
                                             object=DDL.BaseClassList):
        basePreds.update(Collection(ddlMetaGraph,baseClsList))
                                             
    dPreds.difference_update(basePreds)
    return dPreds
def test():
    unittest.main()    
    # import doctest
    # doctest.testmod()

if __name__ == '__main__':
    test()
