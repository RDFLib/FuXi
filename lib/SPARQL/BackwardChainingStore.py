import itertools
from FuXi.Rete.Proof import *
from rdflib import RDFS, RDF, Variable
from rdflib.util import first
from rdflib.store import Store
from rdflib.store.REGEXMatching import NATIVE_REGEX
from rdflib.sparql.Algebra import *
from rdflib.sparql.graphPattern import BasicGraphPattern
from rdflib.sparql.bison.Query import Query
from rdflib.Graph import Graph
from FuXi.DLP import DisjunctiveNormalForm
from FuXi.Rete.Magic import *
from FuXi.Rete.TopDown import *
from FuXi.Rete.SidewaysInformationPassing import *
from FuXi.Horn.PositiveConditions import BuildUnitermFromTuple
from FuXi.Rete.Util import lazyGeneratorPeek

class TopDownSPARQLEntailingStore(Store):
    """
    A Store which uses FuXi's sip strategy and the in-memory SPARQL Algebra
    implementation as a store-agnostic, top-down decision procedure for 
    SPARQL OWL2-RL/RIF/N3 entailment  
    """
    context_aware = True
    formula_aware = True
    transaction_aware = True
    regex_matching = NATIVE_REGEX
    batch_unification = True
    def getDerivedPredicates(self,expr,prolog):
        if isinstance(expr,BasicGraphPattern):
            for s,p,o,func in expr.patterns:
                if p in self.derivedPredicates:
                    yield p
                if p == RDF.type and o != p and o in self.derivedPredicates:
                    yield p
        elif isinstance(expr,NonSymmetricBinaryOperator):
            for term in self.getDerivedPredicates(expr.left,prolog):
                yield term
            for term in self.getDerivedPredicates(expr.right,prolog):
                yield term
        else:
            raise NotImplementedError(expr)
    
    def isaBaseQuery(self, query):
        """
        If the given SPARQL query involves purely base predicates 
        it returns it (as a parsed string), otherwise it returns a SPARQL algebra
        instance for top-down evaluation using this store
        
        >>> graph=Graph()
        >>> topDownStore = TopDownSPARQLEntailingStore(graph.store,[RDFS.seeAlso],nsBindings={u'rdfs':RDFS.RDFSNS})
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] rdfs:seeAlso [] }")
        >>> isinstance(rt,(BasicGraphPattern,AlgebraExpression))
        True
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] a [] }")
        >>> isinstance(rt,(Query,basestring))
        True
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] a [] OPTIONAL { [] rdfs:seeAlso [] } }")
        >>> isinstance(rt,(BasicGraphPattern,AlgebraExpression))
        True
        """
        from rdflib.sparql.bison.Query import Prolog
        from rdflib.sparql.parser import parse
        global prolog
        prolog = None
        query = parse(query)
        if not query.prolog:
                query.prolog = Prolog(None, [])
                query.prolog.prefixBindings.update(self.nsBindings)
        else:
            for prefix, nsInst in self.nsBindings.items():
                if prefix not in query.prolog.prefixBindings:
                    query.prolog.prefixBindings[prefix] = nsInst                    
                    
        prolog = query.prolog
        algebra=RenderSPARQLAlgebra(query,nsMappings=self.nsBindings)
        return first(self.getDerivedPredicates(algebra,prolog)) and algebra or query
    
    def __init__(self, store, edb, derivedPredicates=None,idb=None,DEBUG=False,nsBindings={}):
        self.dataset = store
        if hasattr(store,'_db'):
            self._db     = store._db
        self.derivedPredicates = derivedPredicates and derivedPredicates or set()
        self.idb               = idb and idb or set()
        self.edb               = edb
        self.targetGraph       = None
        self.DEBUG             = DEBUG
        self.nsBindings        = nsBindings
        
        #Add a cache of the namespace bindings to use later in coining Qnames in 
        #generated queries
        self.edb.revNsMap         = {}
        self.edb.nsMap            = {}
        for k,v in nsBindings.items():
            self.edb.revNsMap[v] = k
            self.edb.nsMap[k]    = v
        for key,uri in self.edb.namespaces():
            self.edb.revNsMap[uri] = key
            self.edb.nsMap[key]    = uri
        
    def conjunctiveSipStrategy(self,goalsRemaining,sipCollection,factGraph,bindings={}):
        """
        Given a conjunctive set of triples, invoke sip-strategy passing
        on intermediate solutions to facilitate 'join' behavior
        """
        try:
            tp = goalsRemaining.next()
            assert isinstance(bindings,dict)
            for nextAnswer,ns in SipStrategy(
                                             tp,
                                             sipCollection,
                                             factGraph,
                                             self.derivedPredicates,
                                             bindings=bindings,
                                             debug = self.DEBUG,
                                             buildProof = False):
                nonGroundGoal = isinstance(nextAnswer,dict) 
                if nonGroundGoal or nextAnswer:
                    #Either we recieved bindings from top-down evaluation
                    #or we (successfully) proved a ground query
                    if not nonGroundGoal:
                        #Attempt to prove a ground query, return the response
                        rt = nextAnswer
                    else:
                        #Recieved solutions to 'open' query, merge with given bindings
                        #and continue
                        rt = mergeMappings1To2(bindings,nextAnswer)
                    #either answers were provided (the goal wasn't grounded) or
                    #the goal was ground and successfully proved
                    for ansDict in self.conjunctiveSipStrategy(
                                             goalsRemaining,
                                             sipCollection,
                                             factGraph,
                                             rt):
                        yield ansDict
        except StopIteration:
            yield bindings
    
    def batch_unify(self, patterns):
        """
        Perform RDF triple store-level unification of a list of triple
        patterns (4-item tuples which correspond to a SPARQL triple pattern
        with an additional constraint for the graph name).  
        
        Uses the sip-strategy implementation to solve the conjunctive goal
        and yield unified bindings
        
        :Parameters:
        - `patterns`: a list of 4-item tuples where any of the items can be
           one of: Variable, URIRef, BNode, or Literal.
        
        Returns a generator over dictionaries of solutions to the list of
        triple patterns.    
        """
        dPreds=set()
        goals=[]
        for s,p,o,g in patterns:
            goals.append((s,p,o))
            dPreds.add(p == RDF.type and o or p)
        if set(dPreds).intersection(self.derivedPredicates):
            #Patterns involve derived predicates        
            dPreds = self.derivedPredicates.union(dPreds)
            self.edb.adornedProgram = \
                SetupDDLAndAdornProgram(
                    self.edb,
                    self.idb,
                    goals,
                    derivedPreds=dPreds)
    
            sipCollection=PrepareSipCollection(self.edb.adornedProgram)
            if self.DEBUG and sipCollection:
                print >>sys.stderr,"Sideways Information Passing (sip) graph: "
                for sip in SIPRepresentation(sipCollection):
                    print >>sys.stderr,sip
                pprint(list(self.edb.adornedProgram),sys.stderr)
            elif self.DEBUG:
                print >> sys.stderr, "No SIP graph!"
            self.batch_unification = False
            for ansDict in self.conjunctiveSipStrategy(
                                        iter(goals),
                                        sipCollection,
                                        self.edb):
                yield ansDict       
            self.batch_unification = True
        else:
            #conjunctive query involving EDB predicateso only
            vars = []
            triples = []
            for pat in patterns:
                triples.append(BuildUnitermFromTuple(pat[:3]))
                vars.extend([term for term in pat[:3] 
                                if isinstance(term,Variable)])

            query=RDFTuplesToSPARQL(triples,self.edb,vars=vars)
            if self.DEBUG:
                print "Batch unify resolved against EDB"
                print query
            rt = self.edb.query(query,initNs = self.nsBindings)    
            rt = len(vars)>1 and ( dict([(vars[idx],i) 
                                           for idx,i in enumerate(v)]) 
                                                for v in rt ) \
                   or ( dict([(vars[0],v)]) for v in rt )
            for item in rt:
                yield item
            
    def close(self, commit_pending_transaction=False):
        """
        This closes the database connection. The commit_pending_transaction parameter specifies whether to
        commit all pending transactions before closing (if the store is transactional).
        """
        return self.dataset.close(commit_pending_transaction)
    
    def destroy(self, configuration):
        """
        This destroys the instance of the store identified by the configuration string.
        """
        return self.dataset.destroy(configuration)
        
    def triples_choices(self, (subject, predicate, object_),context=None):
        """
        A variant of triples that can take a list of terms instead of a single
        term in any slot.  Stores can implement this to optimize the response time
        from the default 'fallback' implementation, which will iterate
        over each term in the list and dispatch to tripless
        """
        for rt in self.dataset.triples_choices((subject, predicate, object_),context):
            yield rt

    def triples(self, (subject, predicate, object), context=None):
        """
        A generator over all the triples matching the pattern. Pattern can
        include any objects for used for comparing against nodes in the store, for
        example, REGEXTerm, URIRef, Literal, BNode, Variable, Graph, QuotedGraph, Date? DateRange?

        A conjunctive query can be indicated by either providing a value of None
        for the context or the identifier associated with the Conjunctive Graph (if it's context aware).
        """
        for rt in self.dataset.triples((subject, predicate, object), context):
            yield rt

    def __len__(self, context=None):
        """
        Number of statements in the store. This should only account for non-quoted (asserted) statements
        if the context is not specified, otherwise it should return the number of statements in the formula or context given.
        """
        return len(self.dataset)

    def contexts(self, triple=None):
        """
        Generator over all contexts in the graph. If triple is specified, a generator over all
        contexts the triple is in.
        """
        for ctx in self.dataset.contexts(triple):
            yield ctx

    # Optional Namespace methods

    def bind(self, prefix, namespace):
        self.nsBindings[prefix]=namespace
        #self.targetGraph.bind(prefix,namespace)

    def prefix(self, namespace):
        revDict = dict([(v,k) for k,v in self.nsBindings.items()])
        return revDict.get(namespace)

    def namespace(self, prefix):
        return self.nsBindings.get(prefix)

    def namespaces(self):
        for prefix,nsUri in self.nsBindings.items():
            yield prefix,nsUri

    # Optional Transactional methods

    def commit(self):
        self.dataset.commit()

    def rollback(self):
        self.dataset.rollback()
    
def test():
     import doctest
     doctest.testmod()

if __name__ == '__main__':
    test()