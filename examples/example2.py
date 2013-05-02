from rdflib import Variable, Namespace
from rdflib.graph import Graph
from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Rete.Util import generateTokenSet
from FuXi.Horn.HornRules import HornFromN3
from FuXi.Rete.Magic import MagicSetTransformation, AdornLiteral
from FuXi.SPARQL import RDFTuplesToSPARQL

exNs = Namespace('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#')

rules = HornFromN3('http://dev.w3.org/2000/10/swap/test/cwm/fam-rules.n3')
factGraph = Graph().parse(
    'http://dev.w3.org/2000/10/swap/test/cwm/fam.n3', format='n3')
factGraph.bind(u'ex', exNs)
dPreds = [exNs.ancestor]

# Then we setup the RETE-UL network that will be used for calculating the
# closure (or fixpoint) of the magic set-rewritten rules over the fact graph

rule_store, rule_graph, network = SetupRuleStore(makeNetwork=True)
network.nsMap = {u'ex': exNs}
closureDeltaGraph = Graph()
network.inferredFacts = closureDeltaGraph

# Then we build the network from the re-written rules, using our query
# (or goal): "who are the descendants of david"

goals = [(exNs.david, exNs.ancestor, Variable('ANCESTOR'))]

for rule in MagicSetTransformation(factGraph, rules, goals, dPreds):
    network.buildNetworkFromClause(rule)
    # network.rules.add(rule)
    print("\t%s" % rule)

# Then we create a 'magic seed' from the goal and print the goal
# as a SPARQL query

goalLit = AdornLiteral(goals[0])
adornedGoalSeed = goalLit.makeMagicPred()
goal = adornedGoalSeed.toRDFTuple()
print(RDFTuplesToSPARQL([goalLit], factGraph, vars=[Variable('ANCESTOR')]))

# Finally we run the seed fact and the original facts through the magic
# set RETE-UL network

network.feedFactsToAdd(generateTokenSet([goal]))
network.feedFactsToAdd(generateTokenSet(factGraph))
network.reportConflictSet(closureSummary=True)
