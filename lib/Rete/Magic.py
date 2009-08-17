#!/usr/bin/env python
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
"""

import unittest, os, time, itertools, copy
from FuXi.Rete.RuleStore import SetupRuleStore, N3RuleStore, N3Builtin, LOG
from FuXi.Rete.AlphaNode import ReteToken
from FuXi.Horn.HornRules import Clause, Ruleset, Rule, HornFromN3
from FuXi.DLP import FUNCTIONAL_SEMANTCS, NOMINAL_SEMANTICS
from FuXi.Horn.PositiveConditions import *
from FuXi.Syntax.InfixOWL import OWL_NS
from cStringIO import StringIO
from rdflib.Graph import Graph
from rdflib import URIRef, RDF, RDFS, Namespace, Variable, Literal, URIRef
from rdflib.sparql.Algebra import RenderSPARQLAlgebra
from rdflib.sparql.bison import Parse
from rdflib.util import first
#from testMagic import *
from SidewaysInformationPassing import *

EX_ULMAN = Namespace('http://doi.acm.org/10.1145/6012.15399#')
LOG_NS   = Namespace("http://www.w3.org/2000/10/swap/log#")
MAGIC = Namespace('http://doi.acm.org/10.1145/28659.28689#')

RULE_ARC_QUERY=\
"""
SELECT ?arc ?head 
{  
  ?arc a magic:SipArc . 
  ?head a magic:BoundHeadPredicate; ?arc []
}"""

def PrepareSipCollection(adornedRuleset):
    for rule in adornedRuleset:
        ruleHead = GetOp(rule.formula.head)
        print ruleHead, rule
        sipGraph = rule.sip
        SIPRepresentation(sipGraph)
        print sipGraph.serialize(format='n3')
        for arc,ph in sipGraph.query(RULE_ARC_QUERY,
                                     initNs={u'magic':MAGIC}):
            print ph

def SipStrategy(query,sipCollection):
    pass

def MagicSetTransformation(factGraph,rules,GOALS,derivedPreds=None,strictCheck=False,noMagic=[]):
    """
    Takes a goal and a ruleset and returns an iterator
    over the rulest that corresponds to the magic set
    transformation:
    
    [[[
    
    ]]]
    """
    magicPredicates=set()
    if not derivedPreds:
        derivedPreds=list(DerivedPredicateIterator(factGraph,rules))
    replacement={}
    rs=AdornProgram(factGraph,rules,GOALS,derivedPreds)
    if factGraph:
        factGraph.adornedProgram = rs
    newRules=[]
    for rule in rs: 
        magicPositions={}
        #Generate magic rules
        for idx,pred in enumerate(iterCondition(rule.formula.body)):
            magicBody=[]
            if isinstance(pred,AdornedUniTerm):# and pred not in magicPredicates:
                # For each rule r in Pad, and for each occurrence of an adorned 
                # predicate p a in its body, we generate a magic rule defining magic_p a
                prevPreds=[item for _idx,item in enumerate(rule.formula.body)
                                            if _idx < idx]             
                assert 'b' in pred.adornment,"adorned predicate w/out any bound arguments!"
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
        if 'b' in rule.formula.head.adornment:
            headMagicPred=rule.formula.head.makeMagicPred()
            newRule.formula.body.formulae.insert(0,headMagicPred)
        newRules.append(newRule)

    if not newRules:
#        print "No magic set candidates"
        if set([OWL_NS.InverseFunctionalProperty,
                OWL_NS.FunctionalProperty]).intersection(factGraph.objects(predicate=RDF.type)):
            newRules.extend(HornFromN3(StringIO(FUNCTIONAL_SEMANTCS)))
        if (None,OWL_NS.oneOf,None) in factGraph:
            #Only include list and oneOf semantics
            #if oneOf axiom is detected in graph 
            #reduce computational complexity
            newRules.extend(HornFromN3(StringIO(NOMINAL_SEMANTICS)))
    elif strictCheck:
        first(DerivedPredicateIterator(factGraph,newRules,strict=True))
    for rule in newRules:
        yield rule

def NormalizeGoals(goals):
    if isinstance(goals,(list,set)):
        for goal in goals:
            yield goal,{}
    elif isinstance(goals,tuple):
        yield sparqlQuery,{}
    else:
        query=RenderSPARQLAlgebra(Parse(goals))
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
            self.ruleStr+=''.join(pred.toRDFTuple())
        super(AdornedRule, self).__init__(clause,decl,nsMapping)        

    def __hash__(self):
        return hash(self.ruleStr)
        
    def __eq__(self,other):
        return hash(self) == hash(other)   

def NormalizeUniterm(term):
    if isinstance(term,Uniterm):
        return term
    elif isinstance(term,N3Builtin):
        return Uniterm(term.uri,term.argument) 
    
def AdornRule(derivedPreds,clause,newHead):
    """
    Adorns a horn clause using the given new head and list of
    derived predicates
    """
    assert len(list(iterCondition(clause.head)))==1
    sip=BuildNaturalSIP(clause,derivedPreds,newHead)
    bodyPredReplace={}
    for literal in iterCondition(sip.sipOrder):
        args = GetArgs(literal)
        op   = GetOp(literal)
        if op in derivedPreds:
            for N,x in IncomingSIPArcs(sip,getOccurrenceId(literal)): 
                if not set(x).difference(args):
                    # A binding
                    # for q is useful, however, only if it is a binding for an argument of q.
                    bodyPredReplace[literal]=AdornedUniTerm(NormalizeUniterm(literal),
                            [ i in x and 'b' or 'f' for i in args])
                    
#                For a predicate occurrence with no incoming
#                arc, the adornment contains only f‚Äö√Ñ√¥s. For our purposes here, 
#                we do not distinguish between a predicate with such an 
#                adornment and an unadorned predicate                                    
    rule=AdornedRule(Clause(And([bodyPredReplace.get(p,p) 
                                 for p in iterCondition(sip.sipOrder)]),
                            AdornedUniTerm(clause.head,newHead.adornment)))
    rule.sip = sip
    return rule

def AdornProgram(factGraph,rs,goals,derivedPreds=None):
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
        
    >>> ruleStore,ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
    >>> ruleStore._finalize()
    >>> fg=Graph().parse(StringIO(PROGRAM2),format='n3')
    >>> rs,query=AdornProgram(fg,ruleGraph,NON_LINEAR_MS_QUERY)
    >>> for rule in rs: print rule
    Forall ?Y ?X ( ex:sg(?X ?Y) :- ex:flat(?X ?Y) )
    Forall ?Y ?Z4 ?X ?Z1 ?Z2 ?Z3 ( ex:sg(?X ?Y) :- And( ex:up(?X ?Z1) ex:sg(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ex:sg(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )
    >>> print query
    (rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#john'), rdflib.URIRef('http://doi.acm.org/10.1145/6012.15399#sg'), ?X)
    """
    from FuXi.DLP import LloydToporTransformation
#    rs=rs is None and Ruleset(n3Rules=ruleGraph.store.rules,
#               nsMapping=ruleGraph.store.nsMgr) or rs
    
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
        return rt
    def processedAdornedPred(pred,_list):
        for p in _list:
            if GetOp(p) == GetOp(pred) and p.marked:# and p.adornment == pred.adornment:
                return True
        return False
    toDo=unprocessedPreds(adornedPredicateCollection)
    adornedProgram=set()
    while toDo:
        for term in toDo:
            #check if there is a rule with term as its head
            for rule in rs:
                for clause in LloydToporTransformation(rule.formula):
                    head=isinstance(clause.head,Exists) and clause.head.formula or clause.head
                    _a=GetOp(head)
                    _b=GetOp(term)
                    if isinstance(head,Uniterm) and GetOp(head) == GetOp(term):
                        #for each rule that has p in its head, we generate an adorned version for the rule
                        adornedRule=AdornRule(derivedPreds,clause,term)
                        adornedProgram.add(adornedRule)
                        #The adorned version of a rule contains additional adorned
                        #predicates, and these are added
                        for pred in iterCondition(adornedRule.formula.body):
                            aPred = not isinstance(pred,AdornedUniTerm) and AdornLiteral(pred.toRDFTuple(),nsBindings) or pred 
                            if GetOp(pred) in derivedPreds and not processedAdornedPred(aPred,adornedPredicateCollection):
                                adornedPredicateCollection.add(aPred)
            term.marked=True
        toDo=unprocessedPreds(adornedPredicateCollection)
    return adornedProgram

class AdornedUniTerm(Uniterm):
    def __init__(self,uterm,adornment=None):
        self.marked = False
        self.adornment=adornment
        self.nsMgr=uterm.nsMgr
        newArgs=copy.deepcopy(uterm.arg)
        super(AdornedUniTerm, self).__init__(uterm.op,newArgs)
        self.isMagic=False

    def clone(self):
        return AdornedUniTerm(self,self.adornment)
        
    def makeMagicPred(self):
        """
        Make a (cloned) magic predicate
        
        The arity of the new predicate is the number of occurrences of b in the 
        adornment a, and its arguments correspond to the bound arguments of p a
        """
        newAdornedPred=AdornedUniTerm(self,self.adornment)
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
                
    def getDistinguishedVariables(self):
        for idx,term in enumerate(self.arg):
            if self.adornment[idx]=='b' and isinstance(term,Variable):
                yield term
                
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
        if self.op == RDF.type:
            adornSuffix = '_'+self.adornment[0]
        else:
            adornSuffix='_'+''.join(self.adornment)
        if self.isMagic:
            if self.op == RDF.type:
                return "%s(%s)"%(self.normalizeTerm(self.arg[-1]),
                                 self.normalizeTerm(self.arg[0]))
            else:
                return "%s(%s)"%(pred,
                                ' '.join([self.normalizeTerm(i) 
                                            for idx,i in enumerate(self.arg) 
                                                    if self.adornment[idx]=='b']))
        elif self.op == RDF.type:
            return "%s%s(%s)"%(self.normalizeTerm(self.arg[-1]),
                               adornSuffix,
                               self.normalizeTerm(self.arg[0]))
        else:
            return "%s%s(%s)"%(pred,
                               adornSuffix,
                               ' '.join([self.normalizeTerm(i) for i in self.arg]))

def AdornLiteral(rdfTuple,newNss=None):
    """
    An adornment for an n-ary predicate p is a string a of length n on the 
    alphabet {b, f}, where b stands for bound and f stands for free. We 
    assume a fixed order of the arguments of the predicate.
    
    Intuitively, an adorned occurrence of the predicate, p a, corresponds to a 
    computation of the predicate with some arguments bound to constants, and 
    the other arguments free, where the bound arguments are those that are
    so indicated by the adornment.    
    
    >>> EX=Namespace('http://doi.acm.org/10.1145/6012.15399#')
    >>> query=RenderSPARQLAlgebra(Parse(NON_LINEAR_MS_QUERY))
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
    adornment=[ isinstance(term,(Variable,BNode)) and 'f' or 'b' 
                for idx,term in enumerate(opArgs) ]
    return AdornedUniTerm(uTerm,adornment)  

def iterCondition(condition):
    return isinstance(condition,SetOperator) and condition or iter([condition])

def DerivedPredicateIterator(factsOrBasePreds,ruleset,strict=False):
    """
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(MAGIC_PROGRAM1),format='n3')
    >>> ruleStore._finalize()
    >>> ruleFacts=Graph().parse(StringIO(MAGIC_PROGRAM1),format='n3')
    >>> for lit in DerivedPredicateIterator(ruleFacts,ruleGraph): print lit
    ex:anc(?X ?Y)
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(PROGRAM2),format='n3')
    >>> ruleStore._finalize()
    >>> ruleFacts=Graph().parse(StringIO(PROGRAM2),format='n3')    
    >>> for lit in DerivedPredicateIterator(ruleFacts,ruleGraph): print lit
    ex:sg(?X ?Y)
    """
    basePreds=[GetOp(buildUniTerm(fact)) for fact in factsOrBasePreds 
                        if fact[1] != LOG.implies]     
    processed={True:set(),False:set()}
    derivedPreds=set()
    uncertainPreds=set()
    ruleBodyPreds=set()
    ruleHeads=set()
    for rule in ruleset:
        for idx,term in enumerate(itertools.chain(iterCondition(rule.formula.head),
                                  iterCondition(rule.formula.body))):
            op = GetOp(term)
            if op not in processed[idx>0]: 
                if idx > 0:
                    ruleBodyPreds.add(op)
                else:
                    ruleHeads.add(op)
                if strict and not (op not in basePreds or idx > 0):
#                    print term," is a member of a derived predicate and a base predicate!"
                    raise SyntaxError("%s is a member of a derived predicate and a base predicate!"%term)
#                assert op not in basePreds or idx > 0,"Malformed program!"
                if op in basePreds:
                    uncertainPreds.add(op)
                else:
                    if idx == 0 and not isinstance(op,Variable):
                        derivedPreds.add(op)
                    elif not isinstance(op,Variable):
                        uncertainPreds.add(op)
                processed[idx>0].add(op)
    for pred in uncertainPreds:
        if (pred not in ruleBodyPreds and not isinstance(pred,Variable)) or\
           pred in ruleHeads:
            derivedPreds.add(pred)
#    assert not derivedPred.intersection(basePreds),"There are predicates that are both derived and base!"
    for pred in derivedPreds:
        yield pred
    
def IsBasePredicate(ruleGraph,pred):
    pass

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

def NormalizeLPDb(ruleGraph,fact_db):
    """
    For performance reasons, it 1s good to decompose the database into a set of
    pure base predicates (which can then be stored using a standard DBMS)
    and a set of pure derived predicates Fortunately, such a decomposition 1s 
    always possible, because every database can be rewritten ...as 
    database containing only base and derived predicates.    
    
    >>> ruleStore,ruleGraph=SetupRuleStore()
    >>> g=ruleGraph.parse(StringIO(PARTITION_LP_DB_PREDICATES),format='n3')
    >>> ruleStore._finalize()    
    >>> len(ruleStore.rules)
    1
    >>> factGraph=Graph().parse(StringIO(PARTITION_LP_DB_PREDICATES),format='n3')
    >>> rs=Ruleset(n3Rules=ruleStore.rules,nsMapping=ruleStore.nsMgr)
    >>> for i in rs: print i
    Forall ?Y ?X ?Z ( ex:grandfather(?X ?Y) :- And( ex:father(?X ?Z) ex:parent(?X ?Y) ) )
    >>> len(factGraph)
    4
    >>> print [p for p,iter in iter_non_base_non_derived_preds(rs,factGraph)]
    [rdflib.URIRef('http://doi.acm.org/10.1145/16856.16859#grandfather')]
    """
    candidatePreds=False
    rs=Ruleset(n3Rules=ruleGraph.store.rules,
               nsMapping=ruleStore.nsMgr)
    toAdd=[]
    for pred,replFacts in iter_non_base_non_derived_preds(rs,fact_db):
        replPred=URIRef(pred+'_ext')
        for s,p,o in replFacts:
            fact_db.remove((s,p,o))
            toAdd.append((s,replPred,o))
        head=Uniterm(pred,pred.arg)
        body=Uniterm(replPred,pred.arg)
        newRule=Rule(Clause(body,head),
                     [term for term in pred.arg if isinstance(term,Variable)])
        rs.append(newRule)
    return rs

#class AdornProgramTest(unittest.TestCase):
#    def setUp(self):
#        self.ruleStore,self.ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
#        self.ruleStore._finalize()
#        self.ruleStrings=[
#        'Forall ?Y ?X ( :sg_bf(?X ?Y) :- And( :sg_magic(?X) ex:flat(?X ?Y) ) )',
#        'Forall  ( :sg_magic(?Z1) :- And( :sg_magic(?X) ex:up(?X ?Z1) ) )',
#        'Forall ?Z4 ?Y ?X ?Z1 ?Z2 ?Z3 ( :sg_bf(?X ?Y) :- And( :sg_magic(?X) ex:up(?X ?Z1) :sg_magic(?Z1) :sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) :sg_magic(?Z3) :sg_bf(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )',
#        'Forall  ( :sg_magic(?Z3) :- And( :sg_magic(?X) ex:up(?X ?Z1) :sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ) )',
#        ]
#
#    def testAdorn(self):
#        fg=Graph().parse(StringIO(PROGRAM2),format='n3')
#        rules=Ruleset(n3Rules=self.ruleGraph.store.rules,
#                   nsMapping=self.ruleStore.nsMgr)
#        from pprint import pprint;pprint(self.ruleStrings)        
#        for rule in MagicSetTransformation(fg,
#                                           rules,
#                                           NON_LINEAR_MS_QUERY,
#                                           [MAGIC.sg]):
#            self.failUnless(repr(rule) in self.ruleStrings, repr(rule))

class AdornProgramTest(unittest.TestCase):
    def setUp(self):
        self.ruleStore,self.ruleGraph=SetupRuleStore(StringIO(PROGRAM2))
        self.ruleStore._finalize()
        self.ruleStrings=[
        'Forall ?Y ?X ( :sg_bf(?X ?Y) :- And( :sg_magic(?X) ex:flat(?X ?Y) ) )',
        'Forall  ( :sg_magic(?Z1) :- And( :sg_magic(?X) ex:up(?X ?Z1) ) )',
        'Forall ?Z4 ?Y ?X ?Z1 ?Z2 ?Z3 ( :sg_bf(?X ?Y) :- And( :sg_magic(?X) ex:up(?X ?Z1) :sg_magic(?Z1) :sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) :sg_magic(?Z3) :sg_bf(?Z3 ?Z4) ex:down(?Z4 ?Y) ) )',
        'Forall  ( :sg_magic(?Z3) :- And( :sg_magic(?X) ex:up(?X ?Z1) :sg_bf(?Z1 ?Z2) ex:flat(?Z2 ?Z3) ) )',
        ]

    def testAdorn(self):
        fg=Graph().parse(StringIO(PROGRAM2),format='n3')
        rules=Ruleset(n3Rules=self.ruleGraph.store.rules,
                   nsMapping=self.ruleStore.nsMgr)
        from pprint import pprint;pprint(self.ruleStrings)        
        for rule in MagicSetTransformation(fg,
                                           rules,
                                           NON_LINEAR_MS_QUERY,
                                           [MAGIC.sg]):
            self.failUnless(repr(rule) in self.ruleStrings, repr(rule))
        
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
        print "%s :- %s"%(rule.formula.head,rule.formula.body.formulae[0])
    
            
def test():
    unittest.main()    
    # import doctest
    # doctest.testmod()

if __name__ == '__main__':
    test()