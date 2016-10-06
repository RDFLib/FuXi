# -*- coding: utf-8 -*-
import sys
from pprint import pprint
from rdflib import RDF, URIRef, Variable
from rdflib.util import first
from rdflib.store import Store
from rdflib.plugins.stores.regexmatching import NATIVE_REGEX

# from rdflib.plugins.sparql.algebra import RenderSPARQLAlgebra
from rdflib.plugins.sparql.algebra import translateQuery as RenderSPARQLAlgebra
# from rdflib.plugins.sparql.algebra import NonSymmetricBinaryOperator
# from rdflib.plugins.sparql.graph import BasicGraphPattern

from FuXi.Rete.Magic import SetupDDLAndAdornProgram
from FuXi.Rete.Magic import DerivedPredicateIterator
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.TopDown import PrepareSipCollection
from FuXi.Rete.TopDown import RDFTuplesToSPARQL
from FuXi.Rete.TopDown import mergeMappings1To2
from FuXi.Rete.SidewaysInformationPassing import GetOp
from FuXi.Rete.SidewaysInformationPassing import SIPRepresentation
from FuXi.Rete.Util import LOG
from FuXi.LP.BackwardFixpointProcedure import BackwardFixpointProcedure
from FuXi.LP import IdentifyHybridPredicates
from FuXi.Horn.PositiveConditions import BuildUnitermFromTuple
from FuXi.SPARQL import EDBQuery

# for docstring/test purposes
from rdflib import Graph
assert Graph
from rdflib import RDFS
assert RDFS
from rdflib.plugins.sparql.parserutils import Expr as AlgebraExpression
assert AlgebraExpression
from rdflib.plugins.sparql.sparql import Query
assert Query

TOP_DOWN_METHOD = 0
BFP_METHOD = 1

DEFAULT_BUILTIN_MAP = {
    LOG.equal: "%s  = %s",
    LOG.notEqualTo: "%s != %s"
}


class NonSymmetricBinaryOperator(AlgebraExpression):

    def fetchTerminalExpression(self):
        if self.right.name == 'BGP':
            yield self.right
        else:
            for i in self.right.fetchTerminalExpression():
                yield i


class TopDownSPARQLEntailingStore(Store):

    """
    A Store which uses FuXi's magic set "sip strategies" and the in-memory SPARQL Algebra
    implementation as a store-agnostic, top-down decision procedure for
    semanic web SPARQL (OWL2-RL/RIF/N3) entailment regimes.  Exposed
    as a rdflib / layercake-python API for SPARQL datasets with entailment regimes
    Queries are mediated over the SPARQL protocol using global schemas captured
    as SW theories which describe and distinguish their predicate symbols
    """
    context_aware = True
    formula_aware = True
    transaction_aware = True
    regex_matching = NATIVE_REGEX
    batch_unification = True

    def getDerivedPredicates(self, expr, prologue):
        # if isinstance(expr, BasicGraphPattern):
        if expr.name == 'BGP':
            for s, p, o, func in expr.patterns:
                derivedPred = self.derivedPredicateFromTriple((s, p, o))
                if derivedPred is not None:
                    yield derivedPred
        elif isinstance(expr, NonSymmetricBinaryOperator):
            for term in self.getDerivedPredicates(expr.left, prologue):
                yield term
            for term in self.getDerivedPredicates(expr.right, prologue):
                yield term
        else:
            raise NotImplementedError(expr)

    def isaBaseQuery(self, queryString, queryObj=None):
        """
        If the given SPARQL query involves purely base predicates
        it returns it (as a parsed string), otherwise it returns a SPARQL algebra
        instance for top-down evaluation using this store

        >>> graph=Graph()
        >>> topDownStore = TopDownSPARQLEntailingStore(graph.store, graph, derivedPredicates=[RDFS.seeAlso], nsBindings={u"rdfs": str(RDFS)})
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] rdfs:seeAlso [] }")
        >>> isinstance(rt,(BasicGraphPattern, AlgebraExpression))
        True
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] a [] }")
        >>> isinstance(rt,(Query, basestring)) #doctest: +SKIP
        True
        >>> rt=topDownStore.isaBaseQuery("SELECT * { [] a [] OPTIONAL { [] rdfs:seeAlso [] } }")
        >>> isinstance(rt,(BasicGraphPattern, AlgebraExpression))
        True
        """
        from rdflib.plugins.sparql.query import Prologue
        from rdflib.plugins.sparql.parser import parseQuery
        from rdflib.plugins.sparql import sparql as sparqlModule
        if queryObj:
            query = queryObj
        else:
            query = parseQuery(queryString)
        if not query.prologue:
            query.prologue = Prologue(None, [])
            query.prologue.prefixBindings.update(self.nsBindings)
        else:
            for prefix, nsInst in list(self.nsBindings.items()):
                if prefix not in query.prologue.prefixBindings:
                    query.prologue.prefixBindings[prefix] = nsInst

        sparqlModule.prologue = query.prologue
        algebra = RenderSPARQLAlgebra(query, nsMappings=self.nsBindings)
        return first(self.getDerivedPredicates(algebra, sparqlModule.prologue)) and algebra or query

    def __init__(self,
                 store,
                 edb,
                 derivedPredicates=None,
                 idb=None,
                 DEBUG=False,
                 nsBindings={},
                 decisionProcedure=BFP_METHOD,
                 templateMap=None,
                 identifyHybridPredicates=False,
                 hybridPredicates=[]):
        self.dataset = store
        if hasattr(store, '_db'):
            self._db = store._db
        self.idb = idb and idb or set()
        self.edb = edb
        if derivedPredicates is None:
            self.derivedPredicates = list(
                DerivedPredicateIterator(self.edb, self.idb))
        else:
            self.derivedPredicates = derivedPredicates
        self.DEBUG = DEBUG
        self.nsBindings = nsBindings
        self.edb.templateMap = DEFAULT_BUILTIN_MAP if templateMap is None\
            else templateMap
        self.queryNetworks = []
        self.edbQueries = set()
        if identifyHybridPredicates:
            self.hybridPredicates = IdentifyHybridPredicates(edb,
                                                             self.derivedPredicates)
        else:
            self.hybridPredicates = hybridPredicates if hybridPredicates else []

        # Update derived predicate list for synchrony with hybrid predicate
        # rules
        for hybridPred in self.hybridPredicates:
            self.derivedPredicates.remove(hybridPred)
            if isinstance(self.derivedPredicates, list):
                self.derivedPredicates.append(URIRef(hybridPred + u'_derived'))
            elif isinstance(self.derivedPredicates, set):
                self.derivedPredicates.add(URIRef(hybridPred + u'_derived'))
            else:
                import warnings
                warnings.warn(
                    "Collection of derived predicates is neither a list or a set.",
                    RuntimeWarning)

        # Add a cache of the namespace bindings to use later in coining Qnames in
        # generated queries
        self.edb.revNsMap = {}
        self.edb.nsMap = {}
        for k, v in list(nsBindings.items()):
            self.edb.revNsMap[v] = k
            self.edb.nsMap[k] = v
        for key, uri in self.edb.namespaces():
            self.edb.revNsMap[uri] = key
            self.edb.nsMap[key] = uri

    def invokeDecisionProcedure(self, tp, factGraph, bindings, debug, sipCollection):
        isNotGround = first(filter(
                            lambda i: isinstance(i, Variable), tp))
        rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
        bfp = BackwardFixpointProcedure(
            factGraph,
            network,
            self.derivedPredicates,
            tp,
            sipCollection,
            hybridPredicates=self.hybridPredicates,
            debug=self.DEBUG)
        bfp.createTopDownReteNetwork(self.DEBUG)
        # rt = bfp.answers(debug=self.DEBUG)
        self.queryNetworks.append((bfp.metaInterpNetwork, tp))
        self.edbQueries.update(bfp.edbQueries)
        if self.DEBUG:
            print("Goal/Query: ", tp)
            print("Query was not ground"
                  if isNotGround is not None else "Query was ground")
        if isNotGround is not None:
            for item in bfp.goalSolutions:
                yield item, None
        else:
            yield True, None
        if debug:
            print(bfp.metaInterpNetwork)
            bfp.metaInterpNetwork.reportConflictSet(True, sys.stderr)
            for query in self.edbQueries:
                print("Dispatched query against dataset: ", query.asSPARQL())

    def conjunctiveSipStrategy(self, goalsRemaining, factGraph, bindings=None):
        """
        Given a conjunctive set of triples, invoke sip-strategy passing
        on intermediate solutions to facilitate 'join' behavior
        """
        bindings = bindings if bindings else {}
        try:
            tp = next(goalsRemaining)
            assert isinstance(bindings, dict)
            dPred = self.derivedPredicateFromTriple(tp)
            if dPred is None:
                baseEDBQuery = EDBQuery([BuildUnitermFromTuple(tp)],
                                        self.edb,
                                        bindings=bindings)
                if self.DEBUG:
                    print("Evaluating TP against EDB:%s" %
                          baseEDBQuery.asSPARQL())
                query, rt = baseEDBQuery.evaluate()
                # _vars = baseEDBQuery.returnVars
                for item in rt:
                    bindings.update(item)
                for ansDict in self.conjunctiveSipStrategy(
                        goalsRemaining,
                        factGraph,
                        bindings):
                    yield ansDict

            else:
                queryLit = BuildUnitermFromTuple(tp)
                currentOp = GetOp(queryLit)
                queryLit.setOperator(currentOp)
                query = EDBQuery(
                    [queryLit], self.edb, bindings=bindings)
                if bindings:
                    tp = first(query.formulae).toRDFTuple()
                if self.DEBUG:
                    print("Goal/Query: ", query.asSPARQL())
                SetupDDLAndAdornProgram(
                    self.edb,
                    self.idb,
                    [tp],
                    derivedPreds=self.derivedPredicates,
                    ignoreUnboundDPreds=True,
                    hybridPreds2Replace=self.hybridPredicates)

                if self.hybridPredicates:
                    lit = BuildUnitermFromTuple(tp)
                    op = GetOp(lit)
                    if op in self.hybridPredicates:
                        lit.setOperator(URIRef(op + u'_derived'))
                        tp = lit.toRDFTuple()

                sipCollection = PrepareSipCollection(self.edb.adornedProgram)
                if self.DEBUG and sipCollection:
                    for sip in SIPRepresentation(sipCollection):
                        print(sip)
                    pprint(list(self.edb.adornedProgram), sys.stderr)
                elif self.DEBUG:
                    print("No SIP graph.")
                for nextAnswer, ns in self.invokeDecisionProcedure(
                        tp,
                        factGraph,
                        bindings,
                        self.DEBUG,
                        sipCollection):
                    nonGroundGoal = isinstance(nextAnswer, dict)
                    if nonGroundGoal or nextAnswer:
                        # Either we recieved bindings from top-down evaluation
                        # or we (successfully) proved a ground query
                        if not nonGroundGoal:
                            # Attempt to prove a ground query, return the
                            # response
                            rt = nextAnswer
                        else:
                            # Recieved solutions to 'open' query, merge with given bindings
                            # and continue
                            rt = mergeMappings1To2(bindings, nextAnswer)
                        # either answers were provided (the goal wasn't grounded) or
                        # the goal was ground and successfully proved
                        for ansDict in self.conjunctiveSipStrategy(
                                goalsRemaining,
                                factGraph,
                                rt):
                            yield ansDict
        except StopIteration:
            yield bindings

    def derivedPredicateFromTriple(self, triple):
        """
        Given a triple, return its predicate (if derived)
        or None otherwise
        """
        (s, p, o) = triple
        if p in self.derivedPredicates or p in self.hybridPredicates:
            return p
        elif p == RDF.type and o != p and (
                o in self.derivedPredicates or o in self.hybridPredicates):
            return o
        else:
            return None

    def sparql_query(self,
                     queryString,
                     queryObj,
                     graph,
                     dataSetBase,
                     extensionFunctions,
                     initBindings={},
                     initNs={},
                     DEBUG=False):
        """
        The default 'native' SPARQL implementation is based on sparql-p's expansion trees
        layered on top of the read-only RDF APIs of the underlying store
        """
        from rdflib.sparql.Algebra import TopEvaluate
        from rdflib.QueryResult import QueryResult
        from rdflib import plugin
        from rdflib.sparql.bison.Query import AskQuery
        _expr = self.isaBaseQuery(None, queryObj)
        if isinstance(queryObj.query, AskQuery) and \
                _expr.name == 'BGP':
            # isinstance(_expr, BasicGraphPattern):
            # This is a ground, BGP, involving IDB and can be solved directly
            # using top-down decision procedure
            # First separate out conjunct into EDB and IDB predicates
            # (solving the former first)
            from FuXi.SPARQL import EDBQuery
            groundConjunct = []
            derivedConjunct = []
            for s, p, o, func in _expr.patterns:
                if self.derivedPredicateFromTriple((s, p, o)) is None:
                    groundConjunct.append(BuildUnitermFromTuple((s, p, o)))
                else:
                    derivedConjunct.append(BuildUnitermFromTuple((s, p, o)))
            if groundConjunct:
                baseEDBQuery = EDBQuery(groundConjunct, self.edb)
                subQuery, ans = baseEDBQuery.evaluate(DEBUG)
                assert isinstance(ans, bool), ans
            if groundConjunct and not ans:
                askResult = False
            else:
                askResult = True
                for derivedLiteral in derivedConjunct:
                    goal = derivedLiteral.toRDFTuple()
                    # Solve ground, derived goal directly
                    SetupDDLAndAdornProgram(
                        self.edb,
                        self.idb,
                        [goal],
                        derivedPreds=self.derivedPredicates,
                        ignoreUnboundDPreds=True,
                        hybridPreds2Replace=self.hybridPredicates)

                    if self.hybridPredicates:
                        lit = BuildUnitermFromTuple(goal)
                        op = GetOp(lit)
                        if op in self.hybridPredicates:
                            lit.setOperator(URIRef(op + u'_derived'))
                            goal = lit.toRDFTuple()

                    sipCollection = PrepareSipCollection(
                        self.edb.adornedProgram)
                    if self.DEBUG and sipCollection:
                        for sip in SIPRepresentation(sipCollection):
                            print(sip)
                        pprint(list(self.edb.adornedProgram))
                    elif self.DEBUG:
                        print("No SIP graph.")

                    rt, node = first(self.invokeDecisionProcedure(
                        goal,
                        self.edb,
                        {},
                        self.DEBUG,
                        sipCollection))
                    if not rt:
                        askResult = False
                        break
            return plugin.get('SPARQLQueryResult', QueryResult)(askResult)
        else:
            rt = TopEvaluate(queryObj,
                             graph,
                             initBindings,
                             DEBUG=self.DEBUG,
                             dataSetBase=dataSetBase,
                             extensionFunctions=extensionFunctions)
            return plugin.get('SPARQLQueryResult', QueryResult)(rt)

    def batch_unify(self, patterns):
        """
        Perform RDF triple store-level unification of a list of triple
        patterns (4-item tuples which correspond to a SPARQL triple pattern
        with an additional constraint for the graph name).

        Uses a SW sip-strategy implementation to solve the conjunctive goal
        and yield unified bindings

        :Parameters:
        - `patterns`: a list of 4-item tuples where any of the items can be
           one of: Variable, URIRef, BNode, or Literal.

        Returns a generator over dictionaries of solutions to the list of
        triple patterns that are entailed by the regime.
        """
        dPreds = set()
        goals = []
        for s, p, o, g in patterns:
            goals.append((s, p, o))
            dPred = o if p == RDF.type else p
            if dPred in self.hybridPredicates:
                dPreds.add(URIRef(dPred + u'_derived'))
            else:
                dPreds.add(p == RDF.type and o or p)
        if set(dPreds).intersection(self.derivedPredicates):
            # Patterns involve derived predicates
            self.batch_unification = False
            for ansDict in self.conjunctiveSipStrategy(
                    iter(goals),
                    self.edb):
                yield ansDict
            self.batch_unification = True
        else:
            # conjunctive query involving EDB predicateso only
            vars = []
            triples = []
            for pat in patterns:
                triples.append(BuildUnitermFromTuple(pat[:3]))
                vars.extend([term for term in pat[:3]
                             if isinstance(term, Variable)])

            query = RDFTuplesToSPARQL(triples, self.edb, vars=vars)
            if self.DEBUG:
                print("Batch unify resolved against EDB")
                print(query)

            rt = self.edb.query(query, initNs=self.nsBindings)

            rt = len(vars) > 1 and (dict([(vars[idx], i)
                                          for idx, i in enumerate(v)])
                                    for v in rt) \
                or (dict([(vars[0], v)]) for v in rt)
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

    def triples_choices(self, triple, context=None):
        """
        A variant of triples that can take a list of terms instead of a single
        term in any slot.  Stores can implement this to optimize the response time
        from the default 'fallback' implementation, which will iterate
        over each term in the list and dispatch to tripless
        """
        for rt in self.dataset.triples_choices(triple, context):
            yield rt

    def triples(self, triple, context=None):
        """
        A generator over all the triples matching the pattern. Pattern can
        include any objects for used for comparing against nodes in the store, for
        example, REGEXTerm, URIRef, Literal, BNode, Variable, Graph, QuotedGraph, Date? DateRange?

        A conjunctive query can be indicated by either providing a value of None
        for the context or the identifier associated with the Conjunctive Graph (if it's context aware).
        """
        for rt in self.dataset.triples(triple, context):
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
        self.nsBindings[prefix] = namespace
        # self.targetGraph.bind(prefix, namespace)

    def prefix(self, namespace):
        revDict = dict([(v, k) for k, v in list(self.nsBindings.items())])
        return revDict.get(namespace)

    def namespace(self, prefix):
        return self.nsBindings.get(prefix)

    def namespaces(self):
        for prefix, nsUri in list(self.nsBindings.items()):
            yield prefix, nsUri

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

# from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
