from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.Util import generateTokenSet
from rdflib import Graph

rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)

closureDeltaGraph = Graph()
network.inferredFacts = closureDeltaGraph
print(network)

for rule in HornFromN3(
        'http://www.agfa.com/w3c/euler/rdfs-rules.n3',
        additionalBuiltins=None):
    network.buildNetworkFromClause(rule)
print(network)
network.feedFactsToAdd(generateTokenSet(network.inferredFacts))
print(network)
