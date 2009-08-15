#!/usr/local/bin/python
# -*- coding: utf-8 -*-
"""
The language of positive RIF conditions determines what can appear as a body (the
 if-part) of a rule supported by the basic RIF logic. As explained in Section 
 Overview, RIF's Basic Logic Dialect corresponds to definite Horn rules, and the
  bodies of such rules are conjunctions of atomic formulas without negation.
"""
from rdflib import Variable, BNode, URIRef, Literal, Namespace,RDF,RDFS
from rdflib.Collection import Collection
from rdflib.Graph import ConjunctiveGraph,QuotedGraph,ReadOnlyGraphAggregate, Graph
from rdflib.syntax.NamespaceManager import NamespaceManager

OWL    = Namespace("http://www.w3.org/2002/07/owl#")

def buildUniTerm((s,p,o),newNss=None):
    return Uniterm(p,[s,o],newNss=newNss)

class QNameManager(object):
    def __init__(self,nsDict=None):
        self.nsDict = nsDict and nsDict or {}
        self.nsMgr = NamespaceManager(Graph())
        self.nsMgr.bind('owl','http://www.w3.org/2002/07/owl#')
        self.nsMgr.bind('math','http://www.w3.org/2000/10/swap/math#')
        
    def bind(self,prefix,namespace):
        self.nsMgr.bind(prefix,namespace)

class SetOperator(object):
    def repr(self,operator):
        nafPrefix = self.naf and 'not ' or ''
        if len(self.formulae)==1:
            return nafPrefix+repr(self.formulae[0])
        else:
            return "%s%s( %s )"%(nafPrefix,operator,' '.join([repr(i) for i in self.formulae]))
    def remove(self,item):
        self.formulae.remove(item)
        
    def __len__(self):
        return len(self.formulae)

class Condition(object):
    """
    CONDITION   ::= CONJUNCTION | DISJUNCTION | EXISTENTIAL | ATOMIC
    """
    def __iter__(self):
        for f in self.formulae:
            yield f

class And(QNameManager,SetOperator,Condition):
    """
    CONJUNCTION ::= 'And' '(' CONDITION* ')'
    
    >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    And( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
    """
    def __init__(self,formulae=None,naf=False):
        self.naf = naf
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)
        
    def n3(self):
        """
        >>> And([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
        ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])]).n3()
        u'rdfs:comment a rdf:Property .\\n owl:Class a rdfs:Class'
        
        """
#        if not [term for term in self if not isinstance(term,Uniterm)]:
#            g= Graph(namespace_manager = self.nsMgr)
#            g.namespace_manager= self.nsMgr
#            [g.add(term.toRDFTuple()) for term in self]
#            return g.serialize(format='n3')
#        else:
        return u' .\n '.join([i.n3() for i in self])
        
    def __repr__(self):
        return self.repr('And')
    
class Or(QNameManager,SetOperator,Condition):
    """
    DISJUNCTION ::= 'Or' '(' CONDITION* ')'
    
    >>> Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...      Uniterm(RDF.type,[OWL.Class,RDFS.Class])])
    Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) )
    """
    def __init__(self,formulae=None,naf=False):
        self.naf = naf
        self.formulae = formulae and formulae or []
        QNameManager.__init__(self)
        
    def __repr__(self):
        return self.repr('Or')

class Exists(Condition):
    """
    EXISTENTIAL ::= 'Exists' Var+ '(' CONDITION ')'
    >>> Exists(formula=Or([Uniterm(RDF.type,[RDFS.comment,RDF.Property]),
    ...                    Uniterm(RDF.type,[OWL.Class,RDFS.Class])]),
    ...        declare=[Variable('X'),Variable('Y')])
    Exists ?X ?Y ( Or( rdf:Property(rdfs:comment) rdfs:Class(owl:Class) ) )
    """
    def __init__(self,formula=None,declare=None):
        self.formula = formula
        self.declare = declare and declare or []    
    def __iter__(self):
        for term in self.formula: 
            yield term
    def n3(self):
        """
        """
        return self.formula.n3()
        #return u"@forSome %s %s"%(','.join(self.declare),self.formula.n3())
    
    def __repr__(self):
        return "Exists %s ( %r )"%(' '.join([var.n3() for var in self.declare]),
                                   self.formula )
        
class Atomic(Condition):
    """
    ATOMIC ::= Uniterm | Equal | Member | Subclass (| Frame)
    """
    def __iter__(self):
        yield self

class Equal(QNameManager,Atomic):
    """
    Equal ::= TERM '=' TERM
    TERM ::= Const | Var | Uniterm | 'External' '(' Expr ')'
    
    >>> Equal(RDFS.Resource,OWL.Thing)
    rdfs:Resource =  owl:Thing
    """
    def __init__(self,lhs=None,rhs=None):
        self.lhs = lhs
        self.rhs = rhs
        QNameManager.__init__(self)
        
    def __repr__(self):
        left  = self.nsMgr.qname(self.lhs)
        right = self.nsMgr.qname(self.rhs)
        return "%s =  %s"%(left,right)

def BuildUnitermFromTuple((s,p,o),newNss=None):
    return Uniterm(p,[s,o],newNss)

class Uniterm(QNameManager,Atomic):
    """
    Uniterm ::= Const '(' TERM* ')'
    TERM ::= Const | Var | Uniterm
    
    We restrict to binary predicates (RDF triples)
    
    >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property])
    rdf:Property(rdfs:comment)
    """
    def __init__(self,op,arg=None,newNss=None,naf=False):
        self.naf = naf
        self.op = op
        self.arg = arg and arg or []
        QNameManager.__init__(self)
        if newNss is not None:
            newNss = isinstance(newNss,dict) and newNss.items() or newNss
            for k,v in newNss:
                self.nsMgr.bind(k,v)
        self._hash=hash(reduce(lambda x,y:str(x)+str(y),
            len(self.arg)==2 and self.toRDFTuple() or [self.op]+self.arg))
        
    def renameVariables(self,varMapping):
        if self.op == RDF.type:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
        else:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
            self.arg[1]=varMapping.get(self.arg[1],self.arg[1])

    def ground(self,varMapping):
        if self.op == RDF.type:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
        else:
            self.arg[0]=varMapping.get(self.arg[0],self.arg[0])
            self.arg[1]=varMapping.get(self.arg[1],self.arg[1])
                
    def __hash__(self):
        return self._hash
    
    def __eq__(self,other):
        return hash(self) == hash(other)                       
        
    def renderTermAsN3(self,term):
        if term == RDF.type:
            return 'a'
        elif isinstance(term, (BNode,Literal,Variable)):
            return term.n3()
        else:
            return self.nsMgr.qname(term)
        
    def n3(self):
        """
        Serialize as N3 (using available namespace managers)
        
        >>> Uniterm(RDF.type,[RDFS.comment,RDF.Property]).n3()
        u'rdfs:comment a rdf:Property'

        """
        return ' '.join([ self.renderTermAsN3(term) 
                         for term in [self.arg[0],self.op,self.arg[1]]])
        
    def toRDFTuple(self):
        subject,_object = self.arg
        return (subject,self.op,_object)
        
    def collapseName(self,val):
        try:
            rt = self.nsMgr.qname(val)
            if len(rt.split(':')[0])>1 and rt[0]=='_':
                return ':'+rt.split(':')[-1]
            else:
                return rt
                
        except:
            return val
        
    def normalizeTerm(self,term):
        if isinstance(term,Literal):
            return term.n3()
        else:
            return isinstance(term,Variable) and term.n3() or \
                   self.collapseName(term)        
        
    def __repr__(self):
        negPrefix = self.naf and 'not ' or ''
        if self.op == RDF.type:
            arg0,arg1 = self.arg
            return "%s%s(%s)"%(negPrefix,self.normalizeTerm(arg1),self.normalizeTerm(arg0))
        else:
            return "%s%s(%s)"%(negPrefix,self.normalizeTerm(self.op),
                                ' '.join([self.normalizeTerm(i) for i in self.arg]))
            
class PredicateExtentFactory(object):
    """
    Creates an object which when indexed returns
    a Uniterm with the 'registered' symbol and
    two-tuple argument
    
    >>> from rdflib import Namespace, URIRef
    >>> EX_NS = Namespace('http://example.com/')
    >>> ns = {'ex':EX_NS}
    >>> somePredFactory = PredicateExtentFactory(EX_NS.somePredicate,newNss=ns)
    >>> somePredFactory[(EX_NS.individual1,EX_NS.individual2)]
    ex:somePredicate(ex:individual1 ex:individual2)
    >>> somePred2Factory = PredicateExtentFactory(EX_NS.somePredicate,binary=False,newNss=ns)
    >>> somePred2Factory[EX_NS.individual1]
    ex:somePredicate(ex:individual1)
    
    """
    def __init__(self,predicateSymbol,binary=True,newNss=None):
        self.predicateSymbol = predicateSymbol
        self.binary = binary
        self.newNss = newNss
        
    def term(self, name):
        return Class(URIRef(self + name))

    def __getitem__(self, args):
        if self.binary:
            arg1,arg2=args
            return Uniterm(self.predicateSymbol,[arg1,arg2],newNss=self.newNss)
        else:
            return Uniterm(RDF.type,[args,self.predicateSymbol],newNss=self.newNss)
                        
class ExternalFunction(Uniterm):
    """
    An External(ATOMIC) is a call to an externally defined predicate, equality, 
    membership, subclassing, or frame. Likewise, External(Expr) is a call to an 
    externally defined function.
    >>> ExternalFunction(Uniterm(URIRef('http://www.w3.org/2000/10/swap/math#greaterThan'),[Variable('VAL'),Literal(2)]))
    math:greaterThan(?VAL "2"^^<http://www.w3.org/2001/XMLSchema#integer>)
    """
    def __init__(self,builtin,newNss=None):
        from FuXi.Rete.RuleStore import N3RuleStore,N3Builtin
        self.builtin= builtin
        if isinstance(builtin,N3Builtin):
            Uniterm.__init__(self,builtin.uri,[builtin.argument,builtin.result])
        else:
            Uniterm.__init__(self,builtin.op,builtin.arg)
        QNameManager.__init__(self)
        if newNss is not None:
            newNss = isinstance(newNss,dict) and newNss.items() or newNss
            for k,v in newNss:
                self.nsMgr.bind(k,v)
            
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()