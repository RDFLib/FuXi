# -*- coding: utf-8 -*-
"""
"""
import copy, warnings
from rdflib import BNode, RDF, Namespace, Variable, RDFS
from FuXi.Horn.PositiveConditions import And, Or, Uniterm, PredicateExtentFactory, SetOperator,Exists

def HasNestedConjunction(conjunct):
    rt=False
    for item in conjunct:
        if isinstance(item,And):
            rt=True
            break
    return rt

def flattenHelper(condition):
    toDo = [item for item in condition if isinstance(item,And)]
    for i in toDo:
        condition.formulae.remove(i)
    for i in toDo:
        condition.formulae.extend(i)

def HasBreadthFirstNestedConj(condition):
    from FuXi.DLP import breadth_first
    return HasNestedConjunction(condition) or\
           [i for i in breadth_first(condition) 
                if isinstance(i,And) and HasNestedConjunction(i)]

def FlattenConjunctions(condition,isNested=False):
    from FuXi.DLP import breadth_first
    if isNested or HasNestedConjunction(condition):
        flattenHelper(condition)
    for nestedConj in [i for i in breadth_first(condition) 
                       if isinstance(i,And) and HasNestedConjunction(i)]:
        FlattenConjunctions(nestedConj, isNested=True)    

def ApplyDemorgans(clause):
    """
    >>> from FuXi.DLP import Clause
    >>> EX_NS = Namespace('http://example.com/')
    >>> ns = {'ex' : EX_NS}
    >>> pred1 = PredicateExtentFactory(EX_NS.somePredicate,newNss=ns)
    >>> pred2 = PredicateExtentFactory(EX_NS.somePredicate2,newNss=ns)
    >>> pred3 = PredicateExtentFactory(EX_NS.somePredicate3,binary=False,newNss=ns)
    >>> pred4 = PredicateExtentFactory(EX_NS.somePredicate4,binary=False,newNss=ns)
    >>> clause = Clause(And([pred1[(Variable('X'),Variable('Y'))],
    ...                      Or([pred2[(Variable('X'),EX_NS.individual1)],
    ...                          pred3[(Variable('Y'))]],naf=True)]),
    ...                 pred4[Variable('X')])
    >>> clause
    ex:somePredicate4(?X) :- And( ex:somePredicate(?X ?Y) not Or( ex:somePredicate2(?X ex:individual1) ex:somePredicate3(?Y) ) )
    >>> ApplyDemorgans(clause)
    >>> clause
    ex:somePredicate4(?X) :- And( ex:somePredicate(?X ?Y) And( not ex:somePredicate2(?X ex:individual1) not ex:somePredicate3(?Y) ) )
    >>> FlattenConjunctions(clause.body)
    >>> clause
    ex:somePredicate4(?X) :- And( ex:somePredicate(?X ?Y) not ex:somePredicate2(?X ex:individual1) not ex:somePredicate3(?Y) )
    """
    from FuXi.DLP import breadth_first, breadth_first_replace
    replacementMap = {}
    for negDisj in [i for i in breadth_first(clause.body) 
                        if isinstance(i,Or) and i.naf]:
        replacementList = []
        for innerTerm in negDisj:
            assert isinstance(i,Uniterm)
            innerTerm.naf = not innerTerm.naf
            replacementList.append(innerTerm)
        replacementMap[negDisj] = And(replacementList)
    for old,new in replacementMap.items():
        list(breadth_first_replace(clause.body,candidate=old,replacement=new))
        
def HandleNonDisjunctiveClauses(ruleset, network, constructNetwork, negativeStratus, ignoreNegativeStratus, clause):
    from FuXi.DLP import NormalizeClause, ExtendN3Rules, makeRule
    for hc in ExtendN3Rules(network, NormalizeClause(clause), constructNetwork):
        rule = makeRule(hc, network.nsMap)
        if rule.negativeStratus:
            negativeStratus.append(rule)
        if not rule.negativeStratus or not ignoreNegativeStratus:
            ruleset.add(rule)
            
def NormalizeDisjunctions(disj,
                          clause,
                          ruleset,
                          network,
                          constructNetwork,
                          negativeStratus,
                          ignoreNegativeStratus):
    """
    Removes disjunctions from logic programs (if possible)
    """
    from FuXi.DLP import breadth_first, breadth_first_replace
#    disj = [i for i in breadth_first(clause.body) if isinstance(i,Or)]
    while len(disj) > 1:
        ApplyDemorgans(clause)
        if HasBreadthFirstNestedConj(clause.body):
            FlattenConjunctions(clause.body)
        disj=[i for i in breadth_first(clause.body) if isinstance(i,Or)]
        assert len(disj)<2,"Unable to effectively reduce disjunctions"
    if len(disj) == 1:
        #There is one disjunction in the body, we can reduce from:
        #H :- B1 V B2  to H : - B1 and H :- B2 
        origDisj = disj[0]
        for item in origDisj:
            #First we want to replace the entire disjunct with an item within it
            list(breadth_first_replace(clause.body,candidate=origDisj,replacement=item))
            clause_clone = copy.deepcopy(clause)
            disj = [i for i in breadth_first(clause_clone.body) if isinstance(i,Or)]
            if len(disj) > 0:
                #If the formula has disjunctions of it's own, we handle them recursively
                NormalizeDisjunctions(disj,
                                      clause_clone,
                                      ruleset,
                                      network,
                                      constructNetwork,
                                      negativeStratus,
                                      ignoreNegativeStratus)
            else:               
                if HasBreadthFirstNestedConj(clause_clone.body):
                    FlattenConjunctions(clause_clone.body)
                #Otherwise handle normally
                HandleNonDisjunctiveClauses(ruleset, network, constructNetwork, negativeStratus, ignoreNegativeStratus, clause_clone)
            #restore the replaced term (for the subsequent iteration)
            list(breadth_first_replace(clause.body,candidate=item,replacement=origDisj))
    else:
        #The disjunction has been handled by normal form transformation, we just need to 
        #handle normally
        if HasBreadthFirstNestedConj(clause_clone.body):
            FlattenConjunctions(clause_clone.body)        
        HandleNonDisjunctiveClauses(ruleset, network, constructNetwork, negativeStratus, ignoreNegativeStratus, clause)
    
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()
   