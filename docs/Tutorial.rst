==============================================================================
Tutorial - A short description of using FuXi
==============================================================================


-  `Introduction <#Introduction>`_
-  `Forward-chaining Simple Example <#Forward-chaining_Simple_Example>`_
-  `Programmatic Equivalent <#Programmatic_Equivalent>`_
-  `Magic Set Method <#Magic_Set_Method>`_
-  `Backward-chaining inference <#Backward-chaining_inference>`_
-  `SPARQL Entailment / Mediation over Remote
   Endpoints <#SPARQL_Entailment_/_Mediation_over_Remote_Endpoints>`_
-  `Modules <#Modules>`_

Introduction
===============================

`FuXi </p/fuxi/wiki/FuXi>`_ is a multi-modal, logical reasoning system
for the semantic web. It's primary capability is as a a `SPARQL 1.1 RIF
Core Entailment <http://www.w3.org/TR/sparql11-entailment/#RIFCoreEnt>`_
`implementation <http://www.w3.org/2009/sparql/implementations/#sparql11-entailment>`_.
The results in the previous link to the SPARQL 1.1 test result show some
of the semantics it supports.

The role of `FuXi </p/fuxi/wiki/FuXi>`_ for the purpose of inferencing
and the use of on the command-line is discussed in Chapter 10 of Matthew
A. Russell's `Mining the Social
Web <http://shop.oreilly.com/product/0636920010203.do>`_: The Semantic
Web: A Cocktail Discussion (also viewable
`here <http://docs.com/H0WF>`_). There is also a section in the `FuXi
user manual </p/fuxi/wiki/FuXiUserManual#The_Command_Line>`_ wiki
describing the command-line use on this project.

Forward-chaining Simple Example
=====================================================================

As a simple example, consider the following N3 document (hosted from
`http://fuxi.googlecode.com/hg/test/sameAsTestFacts.n3): <http://fuxi.googlecode.com/hg/test/sameAsTestFacts.n3):>`_

::

    @prefix ex: <http://example.org/> .
    @prefix owl: <http://www.w3.org/2002/07/owl#>.

    ex:foo ex:x "xxxx";
           owl:sameAs ex:bar .
    ex:bar ex:y "yyyy" .

and the following N3 rules (hosted here
`http://fuxi.googlecode.com/hg/test/sameAsTestRules.n3): <http://fuxi.googlecode.com/hg/test/sameAsTestRules.n3):>`_

::

    @prefix owl: <http://www.w3.org/2002/07/owl#>.

    { ?x owl:sameAs ?y } => { ?y owl:sameAs ?x } .
    { ?x owl:sameAs ?y . ?x ?p ?o } => { ?y ?p ?o } .

`FuXi </p/fuxi/wiki/FuXi>`_ can apply the rules against the facts
exhaustively via this command-line:

::

    FuXi --input-format=n3 \
         --rules=http://fuxi.googlecode.com/hg/test/sameAsTestRules.n3 \
         http://fuxi.googlecode.com/hg/test/sameAsTestFacts.n3

resulting in the following *inferred* triples (serialized as N3):

::

    @prefix ex: <http://example.org/> .

    ex:bar ex:x "xxxx";
        = ex:bar,
            ex:foo .

    ex:foo ex:y "yyyy";
        = ex:foo .

Note, the **=** is shorthand for owl:sameAs.

Programmatic Equivalent
=====================================================

This can also be done programmatically via the following code:

::

    >>> from rdflib.Graph import Graph
    >>> from FuXi.Rete.RuleStore import SetupRuleStore

    >>> from FuXi.Rete.Util import generateTokenSet
    >>> from FuXi.Horn.HornRules import HornFromN3

    >>> rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
    >>> closureDeltaGraph=Graph()
    >>> network.inferredFacts = closureDeltaGraph
    >>> network
    <Network: 0 rules, 0 nodes, 0 tokens in working memory, 0 inferred tokens>
    >>> for rule in HornFromN3('http://fuxi.googlecode.com/hg/test/sameAsTestRules.n3'): network.buildNetworkFromClause(rule)
    ... 
    <TerminalNode (owl:sameAs(?y ?x) :- owl:sameAs(?x ?y)) (pass-thru): CommonVariables: [?y, ?x] (0 in left, 0 in right memories)>
    <TerminalNode (?p(?y ?o) :- And( owl:sameAs(?x ?y) ?p(?x ?o) )) : CommonVariables: [?x] (0 in left, 0 in right memories)>
    >>> network
    <Network: 2 rules, 4 nodes, 0 tokens in working memory, 0 inferred tokens>
    >>> factGraph = Graph().parse('http://fuxi.googlecode.com/hg/test/sameAsTestFacts.n3',format='n3')
    >>> network.feedFactsToAdd(generateTokenSet(factGraph))
    >>> print closureDeltaGraph.serialize(format='n3')
    @prefix ns1: <http://example.org/> .

    ns1:bar ns1:x "xxxx";
        = ns1:bar,
            ns1:foo .

    ns1:foo ns1:y "yyyy";
        = ns1:foo .

For details of the RETE-UL algorithm implementation (which facilitates
the N3
`forward-chaining <http://en.wikipedia.org/wiki/Forward_chaining>`_
capabilities), see: `documentation of the FuXi.Rete
module </p/fuxi/wiki/FuXiUserManual#FuXi_.Rete>`_

Magic Set Method
=======================================

`FuXi </p/fuxi/wiki/FuXi>`_'s RETE-UL algorithm can be used with the
Generalized Magic Set (GMS) Method in order to re-write a set of rules
to apply to a set of facts according to an apriori query such that
evaluating the re-written rules against the facts is much more efficient
than doing it *naively* as we do above:

::

    from rdflib import Variable, Namespace
    from rdflib.Graph import Graph
    from FuXi.Rete.RuleStore import SetupRuleStore
    from FuXi.Rete.Util import generateTokenSet
    from FuXi.Horn.HornRules import HornFromN3
    from FuXi.Rete.Magic import MagicSetTransformation, AdornLiteral
    from FuXi.SPARQL import RDFTuplesToSPARQL

    exNs = Namespace('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#')

    rules = HornFromN3('http://dev.w3.org/2000/10/swap/test/cwm/fam-rules.n3')
    factGraph = Graph().parse('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3',format='n3')
    factGraph.bind(u'ex',exNs)
    dPreds = [exNs.ancestor]

The contents of fam.n3 are:

::

    @prefix : <fam.n3#>.

    albert begat bill, bevan.
    bill begat carol, charlie.
    bertha begat carol, charlie.
    bevan begat chaude, christine.
    christine begat david, diana, douglas.

The contents of fam-rules.n3 are:

::

    @prefix : <fam.n3#>.

    { ?x begat ?y } => { ?y ancestor ?x }.
    { ?x ancestor ?y. ?y ancestor ?z } => { ?x ancestor ?z }.

Then we setup the RETE-UL network that will be used for calculating the
closure (or fixpoint) of the magic set-rewritten rules over the fact
graph

::

    rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
    network.nsMap = {u'ex':exNs}
    closureDeltaGraph=Graph()
    network.inferredFacts = closureDeltaGraph

Then we build the network from the re-written rules, using our query (or
goal): "who are the descendants of david"

::

    goals = [(exNs.david,exNs.ancestor,Variable('ANCESTOR'))]
    for rule in MagicSetTransformation(factGraph,rules,goals,dPreds):
        network.buildNetworkFromClause(rule)    
        # network.rules.add(rule)
        print "\t", rule

Then we create a 'magic seed' from the goal and print the goal as a
SPARQL query

::

    goalLit = AdornLiteral(goals[0])
    adornedGoalSeed = goalLit.makeMagicPred()
    goal=adornedGoalSeed.toRDFTuple()
    print RDFTuplesToSPARQL([goalLit],factGraph,vars=[Variable('ANCESTOR')])
    SELECT ?ANCESTOR {  <http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#david> <http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#ancestor> ?ANCESTOR }

Finally we run the seed fact and the original facts through the magic
set RETE-UL network

::

    >>> network.feedFactsToAdd(generateTokenSet([goal]))
    >>> network.feedFactsToAdd(generateTokenSet(factGraph))
    >>> network.reportConflictSet(closureSummary=True)
    ..snip...
    @prefix ns1: <http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#> .

    ns1:david ns1:ancestor ns1:albert,
            ns1:bevan,
            ns1:christine .

    ns1:christine a ns1:ancestor_magic;
        ns1:ancestor ns1:albert,
            ns1:bevan .

    ns1:bevan a ns1:ancestor_magic;
        ns1:ancestor ns1:albert .

    ns1:albert a ns1:ancestor_magic .

Note that the only ns1:ancestor triples inferred are those for david
(i.e., the inference space was restricted to only that which is
necessary to answer our query/goal)

For more details on the magic set capabilities, see
`documentation </p/fuxi/wiki/FuXiUserManual#FuXi_.Rete.Magic>`_ on the
`FuXi </p/fuxi/wiki/FuXi>`_.Rete.Magic module and the section on the
`section </p/fuxi/wiki/Overview#Sideways_Information_Passing>`_ in the
overview on the general *Sideways Information Passing* capabilities

Backward-chaining inference
=============================================================

As mentioned earlier, the primary capability of
`FuXi </p/fuxi/wiki/FuXi>`_ is SPARQL 1.1 entailment. This can be
demonstrated using the previous example rules and facts:

::

    >>> from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
    >>> from FuXi.Horn.HornRules import HornFromN3
    >>> from rdflib.Graph import Graph
    >>> from rdflib import Namespace
    >>> from pprint import pprint

    >>> famNs = Namespace('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#')
    >>> nsMapping = {u'fam' : famNs}
    >>> rules = HornFromN3('http://dev.w3.org/2000/10/swap/test/cwm/fam-rules.n3')
    >>> factGraph = Graph().parse('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3',format='n3')
    >>> factGraph.bind(u'fam',famNs)
    >>> dPreds = [famNs.ancestor]

Next we instantiate a
`TopDownSPARQLEntailingStore <http://fuxi.googlecode.com/hg/documentation/html/index.html#FuXi.SPARQL.BackwardChainingStore.TopDownSPARQLEntailingStore>`_,
which is an `rdflib <https://github.com/RDFLib>`_ /
`layercake-python <http://code.google.com/p/python-dlp/wiki/LayerCakePythonDivergence>`_
`Store <http://rdflib.readthedocs.org/en/latest/_modules/rdflib/store.html>`_
which implements a `SPARQL 1.1 RIF Core
Entailment <http://www.w3.org/TR/sparql11-entailment/#RIFCoreEnt>`_
regime, where the queried RDF graph is given by the user (the second
argument) and, along with the given rules (the **idb** keyword
argument), comprises a *RIF-RDF combination*.

The answers given are those that are entailed by the combination.

::

    >>> topDownStore=TopDownSPARQLEntailingStore(
    ...                 factGraph.store,
    ...                 factGraph,
    ...                 idb=rules,
    ...                 derivedPredicates = dPreds,
    ...                 nsBindings=nsMapping)
    >>> targetGraph = Graph(topDownStore)
    >>> targetGraph.bind(u'ex',famNs)      
    >>> pprint(list(targetGraph.query('SELECT ?ANCESTOR { fam:david fam:ancestor ?ANCESTOR }',initNs=nsMapping)))
    [rdflib.URIRef('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#albert'),
     rdflib.URIRef('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#bevan'),
     rdflib.URIRef('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#christine')]

For more about how the user can specify a mapping from (N3) built-ins
used in the given ruleset to SPARQL FILTER expressions via the
**templateMap** argument and how such a mapping can be described in RDF,
see the `SPARQL FILTER Templates and Top Down Builtins
section </p/fuxi/wiki/FuXiUserManual#SPARQL_FILTER_Templates_and_Top_Down_Builtins>`_
in the user manual. Also, see `Builtin infrastructure
(overview) </p/fuxi/wiki/Overview#Builtin_Infrastructure>`_ and `Data
Description Language (for describing SPARQL filter templates and the
derived predicates to use) </p/fuxi/wiki/DataDescriptionLanguage>`_

SPARQL Entailment / Mediation over Remote Endpoints
==============================================================================

This backward-chaining capability can be invoked against existing SPARQL
endpoints using the command-line and is demonstrated in the last section
of the TopDownSW wiki. This can be done programmatically by *wrapping* a
`Generic SPARQL
Store <http://code.google.com/p/python-dlp/wiki/LayerCakePythonDivergence#Generic_SPARQL_Store>`_
with a !TopDownSPARQLEntailingStore instance. Thus, by providing a
description of the dataset along with a rule-set to use, answers
according to a SPARQL 1.1 RIF entailment regime can be returned from an
existing SPARQL endpoint.

`Triclops <http://code.google.com/p/python-dlp/wiki/Triclops>`_ can be
configured to use this capability along with its Proxy SPARQL Endpoint
capabilities to setup a *SPARQL `reverse
proxy <http://en.wikipedia.org/wiki/Reverse_proxy>`_* with entailment
capabilities.

Modules
=====================

The various Python modules are enumerated and discussed in detail
`here </p/fuxi/wiki/FuXiUserManual#The_Primary_Modules>`_

