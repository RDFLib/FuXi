from rdflib.graph import Graph
from FuXi.Rete.RuleStore import SetupRuleStore

from FuXi.Rete.Util import generateTokenSet
from FuXi.Horn.HornRules import HornFromN3


def main():
    rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
    closureDeltaGraph = Graph()
    network.inferredFacts = closureDeltaGraph

    print("N0", network)

    hornrules = HornFromN3('https://raw.githubusercontent.com/RDFLib/FuXi/master/test/sameAsTestRules.n3')

    for rule in hornrules:
        network.buildNetworkFromClause(rule)

    print("N1", network)

    factGraph = Graph().parse(
        'https://raw.githubusercontent.com/RDFLib/FuXi/master/test/sameAsTestFacts.n3', format='n3')
    network.feedFactsToAdd(generateTokenSet(factGraph))
    print(closureDeltaGraph.serialize(format='n3'))

#import pycallgraph
#import sys
#pycallgraph.start()
#main()
#pycallgraph.make_dot_graph('example1.png')
#sys.exit(1)
from pycallgraph import PyCallGraph
from pycallgraph.output import GraphvizOutput

graphviz = GraphvizOutput()
graphviz.output_file = 'example1.png'

with PyCallGraph(output=graphviz):
    main()
