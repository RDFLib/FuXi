==============================================================================
TopDownSW
==============================================================================

Introduction
===============================

The wiki describes and documents `FuXi </p/fuxi/wiki/FuXi>`_'s
`BackwardsChainingStore <http://code.google.com/p/fuxi/source/browse/lib/SPARQL/BackwardChainingStore.py>`_
- an rdflib Store that serves as a query mediation wrapper over an
existing RDFLib graph. The main use is to be able to pose queries
involving terms from a ruleset and/or ontology such that either of the
top-down algorithms (BFP or SLD) are used to answer the queries and
dispatching queries at the bottom of the resolution tree involving EDB
predicates against the given graph. Query mediation can also be used
against a remote SPARQL service using the generic SPARQL store provided
by
`layercake-python <http://code.google.com/p/python-dlp/wiki/LayerCakePythonDivergence>`_.

Details
=====================

The store uses the two "sip strategies" and the in-memory, rdflib SPARQL
Algebra implementation as a store-agnostic, top-down decision procedure
for semanic web SPARQL (OWL2-RL/RIF/N3) entailment regimes. Queries are
mediated over the SPARQL protocol using global schemas captured as SW
theories which describe and distinguish their predicate symbols

The store is instantiated this way:

::

                topDownDPreds = defaultDerivedPreds  if options.ddlGraph else None
                topDownStore=TopDownSPARQLEntailingStore(
                                factGraph.store,
                                factGraph,
                                idb=ruleSet,
                                derivedPredicates = derivedPredicatesIDB,
                                nsBindings=...
                                decisionProcedure = TOP_DOWN_METHOD(0) or 1,
                                identifyHybridPredicates = ..True if you want to scan EDB for predicate symbols ... )
                targetGraph = Graph(topDownStore)
    #            queryLiteral = EDBQuery([BuildUnitermFromTuple(goal) for goal in goals],targetGraph)
                result = targetGraph.query(..query string..,initNs=,regular arguments to query)

Example: Influenza SPARQL entailment / query answering via OWL 2 RL document
============================================================================

Use

::

    drugbank:interactionForDrug 
      a owl:ObjectProperty;
      owl:inverseOf drugbank:interactionDrug1, drugbank:interactionDrug2 .

    drugbank:InfluenzaDrug a owl:Class.

    [
       a owl:Restriction;
       owl:onProperty drugbank:affectedOrganism;
       owl:hasValue "Influenza Virus"
    ] rdfs:subClassOf drugbank:InfluenzaDrug .

    drugbank:affectedOrganism a owl:DatatypeProperty

::

    ( 
      drugbank:InfluenzaDrug 
    ) a ddl:DerivedClassList .

    ( drugbank:interactionForDrug ) a ddl:DerivedPropertyList .

::

    $ FuXi \
    --output=rif --safety=loose --strictness=loose \
    --ddlGraph=test/drugBankDDL.n3 --method=sld 
    --output=n3 \
    --why="SELECT ?label { ?drug a drugbank:InfluenzaDrug; rdfs:label ?label }" 
    --debug --ontology=test/drugBankOnt.n3 
    --ontologyFormat=n3 
    --builtinTemplates=http://fuxi.googlecode.com/hg/RuleBuiltinSPARQLTemplates.n3 
    --sparqlEndpoint --dlp http://www4.wiwiss.fu-berlin.de/drugbank/sparql

    ## Full SPARQL Algebra expression ##
    BGP((?drug,rdf:type,drugbank:InfluenzaDrug),(?drug,rdfs:label,?label))
    ###################################
    No SIP graph!
    Goal/Query:  (?drug, rdflib.URIRef('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'), rdflib.URIRef('http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugbank/InfluenzaDrug'))
        Solving :InfluenzaDrug(?drug) {}
        Processing rule :InfluenzaDrug_f(?X) :- drugbank:affectedOrganism(?X "Influenza Virus")
            Solving :affectedOrganism(?X "Influenza Virus") {}
    SELECT ?X {     ?X <http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugbank/affectedOrganism> "Influenza Virus" }-> []
    FtWarning: Creation of InputSource without a URI
    Evaluating TP against EDB:  SELECT ?label {     <http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugs/DB00198> <http://www.w3.org/2000/01/rdf-schema#label> ?label }
    Time to reach answer Oseltamivir via top-down SPARQL sip strategy: 731.135129929 milli seconds

    $ FuXi \
      --output=rif \
      --safety=loose \
      --strictness=loose \
      --ddlGraph=test/drugBankDDL.n3 \
      --method=bfp \
      --output=n3 \
      --why="SELECT ?label { ?drug a drugbank:InfluenzaDrug; rdfs:label ?label }" \
      --debug \
      --ontology=test/drugBankOnt.n3 \
      --ontologyFormat=n3 \
      --builtinTemplates=http://fuxi.googlecode.com/hg/RuleBuiltinSPARQLTemplates.n3 \
      --sparqlEndpoint \
      --dlp http://www4.wiwiss.fu-berlin.de/drugbank/sparql

    ## Full SPARQL Algebra expression ##
    BGP((?drug,rdf:type,drugbank:InfluenzaDrug),(?drug,rdfs:label,?label))
    ###################################
    No SIP graph!
    Goal/Query:  (?drug, rdflib.URIRef('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'), rdflib.URIRef('http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugbank/InfluenzaDrug'))
    Time to build production rule (RDFLib): 0.000101089477539 seconds
        1. Forall ?X ( :InfluenzaDrug_f(?X) :- drugbank:affectedOrganism(?X "Influenza Virus") )

    (a, 1)     : Forall ?X ( :InfluenzaDrug_f(?X) :- And( :OpenQuery(:InfluenzaDrug) bfp:evaluate(rule:1 1) ) )
    (b, 1)     : Forall  ( bfp:evaluate(rule:1 0) :- :OpenQuery(:InfluenzaDrug) )
    (c, 1, 1) : Forall ?X ( bfp:evaluate(rule:1 1) :- And( bfp:evaluate(rule:1 0) drugbank:affectedOrganism(?X "Influenza Virus") ) )
    (d, 1, 1) : Forall ?X ( :affectedOrganism_query(?X "Influenza Virus") :- bfp:evaluate(rule:1 0) )

    Asserting initial BFP query  :OpenQuery(:InfluenzaDrug)
    Query triggered for  :affectedOrganism_query(?X "Influenza Virus") :- bfp:evaluate(rule:1 0)
    FtWarning: Creation of InputSource without a URI
    SELECT ?X {     ?X <http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugbank/affectedOrganism> "Influenza Virus" }-> []
        Answer to BFP triggered query drugbank:affectedOrganism(:DB00198 "Influenza Virus") : {?X: rdflib.URIRef('http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugs/DB00198')}
    Goal/Query:  (?drug, rdflib.URIRef('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'), rdflib.URIRef('http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugbank/InfluenzaDrug'))
    Query was not ground
    Evaluating TP against EDB:  SELECT ?label {     <http://www4.wiwiss.fu-berlin.de/drugbank/resource/drugs/DB00198> <http://www.w3.org/2000/01/rdf-schema#label> ?label }
    FtWarning: Creation of InputSource without a URI
    Time to reach answer Oseltamivir via top-down SPARQL sip strategy: 725.481987 milli seconds

