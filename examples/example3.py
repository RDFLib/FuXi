from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from FuXi.Horn.HornRules import HornFromN3
from rdflib.graph import Graph
from rdflib import Namespace
from pprint import pprint

famNs = Namespace('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#')
nsMapping = {u'fam': famNs}
rules = HornFromN3('http://dev.w3.org/2000/10/swap/test/cwm/fam-rules.n3')
factGraph = Graph().parse(
    'http://dev.w3.org/2000/10/swap/test/cwm/fam.n3', format='n3')
factGraph.bind(u'fam', famNs)
print(factGraph.serialize(format="n3"))

dPreds = [famNs.ancestor]
topDownStore = TopDownSPARQLEntailingStore(
                factGraph.store,
                factGraph,
                idb=rules,
                derivedPredicates=dPreds,
                nsBindings=nsMapping)
targetGraph = Graph(topDownStore)
targetGraph.bind(u'ex', famNs)
pprint(list(
    targetGraph.query(
        'SELECT ?ANCESTOR { fam:david fam:ancestor ?ANCESTOR }',
    initNs=nsMapping)))
