import copy
from itertools import chain
from FuXi.Horn.PositiveConditions import QNameManager,SetOperator, Condition, Or, And
from FuXi.Rete.Util import selective_memoize
from FuXi.Rete.RuleStore import *
from FuXi.Rete.Proof import ImmutableDict
from rdflib import URIRef, RDF, Namespace, Variable, Literal
from rdflib.util import first
from FuXi.Rete.BetaNode import project
from FuXi.Rete.SidewaysInformationPassing import GetArgs, iterCondition, GetOp, GetVariables

def normalizeBindingsAndQuery(vars,bindings,conjunct):
    """
    Takes a query in the form of a list of variables to bind to
    an a priori set of bindings and a conjunct of literals and applies the bindings
    returning:
     - The remaining variables that were not substituted
     - The (possibly grounded) conjunct of literals
     - The bindings minus mappings involving substituted variables 
    
    """
    _vars = set(vars)
    bindingDomain = set(bindings.keys())
    appliedBindings = False
    if bindings:
        #Apply a priori substitutions
        for lit in conjunct:
            substitutedVars = bindingDomain.intersection(lit.toRDFTuple())
            lit.ground(bindings)
            if substitutedVars:
                appliedBindings = True
                _vars.difference_update(substitutedVars)
    return list(_vars),conjunct, \
           project(bindings,_vars,inverse=True) if appliedBindings else bindings

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
   elif isinstance(term,Literal):
       return term.n3()
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

           prefix = "%s a ?KIND"%first([first(iterCondition(lit)).arg[0].n3() for lit in conjunct])
       conjunct = ( i.formulae[0] if isinstance(i,And) else i for i in conjunct )
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

#@selective_memoize([0,1],['vars','symmAtomicInclusion'])
def RunQuery(subQueryJoin,
            bindings,
            factGraph,
            vars=None,
            debug = False,
            symmAtomicInclusion = False):
   initialNs = hasattr(factGraph,'nsMap') and factGraph.nsMap or \
               dict([(k,v) for k,v in factGraph.namespaces()])

   if not subQueryJoin:
       return False
   if not vars:
       vars=[]
   if bool(bindings):
       #Apply a priori substitutions
       openVars,conjGroundLiterals,bindings  = \
               normalizeBindingsAndQuery(set(vars),
                                         bindings,
                                         subQueryJoin)
       vars=list(openVars)
   else:
       conjGroundLiterals = subQueryJoin
   isGround = not vars
   subquery = RDFTuplesToSPARQL(conjGroundLiterals,
                                factGraph,
                                isGround,
                                [v for v in vars],
                                symmAtomicInclusion)
   rt = factGraph.query(subquery,
                        initNs = initialNs)#,
                        #DEBUG = debug)
   projectedBindings = vars and project(bindings,vars) or bindings
   if isGround:
       if debug:
           print >>sys.stderr, "%s%s-> %s"%(
                         subquery,
                         projectedBindings and 
                         " %s apriori binding(s)"%len(projectedBindings) or '',
                         rt.askAnswer[0])
       return subquery,rt.askAnswer[0]
   else:
       rt = len(vars)>1 and ( dict([(vars[idx],i) 
                                      for idx,i in enumerate(v)]) 
                                           for v in rt ) \
              or ( dict([(vars[0],v)]) for v in rt )
       if debug:
           print >>sys.stderr, "%s%s-> %s"%(
                   subquery,
                   projectedBindings and 
                   " %s apriori binding(s)"%len(projectedBindings) or '',                                
                   rt and '[]')# .. %s answers .. ]'%len(rt) or '[]')
       return subquery,rt

class EDBQuery(QNameManager,SetOperator,Condition):
    """
    A list of frames (comprised of EDB predicates) meant for evaluation over a large EDB
    
    lst is a conjunct of terms
    factGraph is the RDF graph to evaluate queries over
    returnVars is the return variables (None, the default, will cause the list
     to be built via instrospection on lst)
    bindings is a solution mapping to apply to the terms in lst 
    
    
    """
    def __init__(self, 
                 lst, 
                 factGraph,                  
                 returnVars=None, 
                 bindings={}, 
                 varMap={}, 
                 symIncAxMap = {}, 
                 symmAtomicInclusion = False):
        self.factGraph           = factGraph
        self.varMap              = varMap
        self.symmAtomicInclusion = symmAtomicInclusion
        self.formulae            = lst
        self.naf                 = False

        #apply an apriori solutions
        if bool(bindings):
            #Apply a priori substitutions
            openVars,termList,bindings  = \
                    normalizeBindingsAndQuery(set(returnVars) 
                        if returnVars else [v for v in self.getOpenVars()],
                                              bindings,
                                              lst)
            self.returnVars = list(openVars)
        else:
            if returnVars is None:
                #return vars not specified, but meant to be determined by 
                #constructor 
                self.returnVars = self.getOpenVars()
            else:
                #Note if returnVars is an empty list, this
                self.returnVars = (returnVars if isinstance(returnVars,list) 
                                      else list(returnVars)) if returnVars else []
            termList = lst
            
        super(EDBQuery, self).__init__(termList)
        self.bindings            = bindings.normalize() \
                                        if isinstance(
                                            bindings,
                                            ImmutableDict) else bindings

    def copy(self):
        """
        A shallow copy of an EDB query
        """
        return EDBQuery([copy.deepcopy(t) for t in self.formulae],
                        self.factGraph,
                        self.returnVars,
                        self.bindings.copy(),
                        self.varMap.copy(),
                        symmAtomicInclusion = self.symmAtomicInclusion)
        
    def renameVariables(self, varMap):
        for item in self.formulae:
            item.renameVariables(varMap)
        
    def ground(self,mapping):
        appliedVars = set()
        for item in self.formulae:
            if isinstance(item,Or):
                for _item in item.formulae:
                    appliedVars.update(item.ground(mapping))
            else:
                appliedVars.update(item.ground(mapping))
        self.bindings = project(self.bindings,appliedVars,True)
        return appliedVars
                
    def accumulateBindings(self, bindings):
        """
        """
        self.bindings.update(project(bindings,self.getOpenVars(),inverse=True))

    def getOpenVars(self):
        return list(
                 set(
                   reduce(
                     lambda x,y:x+y,
                     map(lambda arg:list(GetVariables(arg,secondOrder=True)),
                         self.formulae))))

    def applyMGU(self,substitutions):
        for term in self.formulae:
            term.renameVariables(substitutions)
        self.bindings = dict([(substitutions.get(k,k),v) 
                            for k,v in self.bindings.items()])

    def evaluate(self,debug = False, symmAtomicInclusion = False):
        return     RunQuery(self.formulae,
                            self.bindings,
                            self.factGraph,
                            vars=self.returnVars,
                            debug = debug,
                            symmAtomicInclusion = symmAtomicInclusion)
        
    def asSPARQL(self):
        initialNs = hasattr(self.factGraph,'nsMap') and self.factGraph.nsMap or \
                    dict([(k,v) for k,v in self.factGraph.namespaces()])
        return RDFTuplesToSPARQL(self.formulae,
                                 self.factGraph,
                                 not self.returnVars,
                                 self.returnVars,
                                 self.symmAtomicInclusion)
        
    def __hash__(self):
        from FuXi.Rete.Network import HashablePatternList
        conj=HashablePatternList(
                    [term.toRDFTuple() for term in self.formulae],
                    skipBNodes=True)
        return hash(conj) 
        
    def extend(self, query, newVarMap = None):
        assert not query.symmAtomicInclusion  
        assert not self.symmAtomicInclusion  
        if newVarMap:
            query.renameVariables(newVarMap)
            self.varMap.update(newVarMap)
        self.formulae.extend([term for term in query.formulae 
                                if term not in self.formulae])
        self.bindings.update(query.bindings)
        
    def __repr__(self):
        return "EDBQuery(%s%s)"%(self.repr(self.symmAtomicInclusion and 'Or' or 'And'),
                       self.bindings and ',%s'%self.bindings or '')
        
def test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    test()