# https://groups.google.com/d/msg/fuxi-discussion/4r1Nt_o1Hco/4QQ7BaqBCH8J
from rdflib.graph import Graph
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.Util import generateTokenSet
# from FuXi.DLP.DLNormalization import NormalFormReduction
from FuXi.Horn.HornRules import HornFromN3
from io import StringIO

rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)

rules = u"""
@prefix owl: <http://www.w3.org/2002/07/owl#> .
{ ?x owl:sameAs ?y } => { ?y owl:sameAs ?x } .
{ ?x owl:sameAs ?y . ?x ?p ?o } => { ?y ?p ?o } .
"""

for rule in HornFromN3(StringIO(rules)):
    network.buildNetworkFromClause(rule)

facts = """
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix ex: <http://example.org/> .
@prefix exterms: <http://example.org/terms/> .
ex:foo
        a exterms:Something ;
        exterms:hasX "blah blah" ;
        owl:sameAs ex:bar .
ex:bar
        exterms:hasY "yyyy" .
"""
g = Graph()
g.parse(data=facts, format="n3")

network.feedFactsToAdd(generateTokenSet(g))

print(network.inferredFacts.serialize(format="n3"))
