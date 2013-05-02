from rdflib.graph import Graph
from FuXi.Rete.RuleStore import SetupRuleStore

from FuXi.Rete.Util import generateTokenSet
from FuXi.Horn.HornRules import HornFromN3


def main():
    rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
    closureDeltaGraph = Graph()
    network.inferredFacts = closureDeltaGraph

    print("N0", network)

    hornrules = HornFromN3('http://fuxi.googlecode.com/hg/test/sameAsTestRules.n3')

    for rule in hornrules:
        network.buildNetworkFromClause(rule)

    print("N1", network)

    factGraph = Graph().parse(
        'http://fuxi.googlecode.com/hg/test/sameAsTestFacts.n3', format='n3')
    network.feedFactsToAdd(generateTokenSet(factGraph))
    print(closureDeltaGraph.serialize(format='n3'))

import pycallgraph
import sys
pycallgraph.start_trace()
main()
pycallgraph.make_dot_graph('example1.png')
sys.exit(1)
