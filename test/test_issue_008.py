# -*- coding: utf-8 -*-
"""
https://github.com/RDFLib/FuXi/issues/8
"""
import unittest
# from FuXi.Rete.RuleStore import SetupRuleStore
from FuXi.Horn.HornRules import HornFromN3
from FuXi.SPARQL.BackwardChainingStore import TopDownSPARQLEntailingStore
from rdflib import Graph  # , ConjunctiveGraph
from rdflib import Namespace
try:
    from io import StringIO
    assert StringIO
except ImportError:
    from cStringIO import StringIO

rules = """\
@prefix : <fam.n3#>.
@keywords is, of, a.
{ ?x begat ?y } => { ?y ancestor ?x }.
{ ?x ancestor ?y. ?y ancestor ?z } => { ?x ancestor ?z }."""

facts = """\
@prefix : <fam.n3#>.
@keywords is, of, a.

albert begat bill, bevan.
bill begat carol, charlie.
bertha begat carol, charlie.
bevan begat chaude, christine.
christine begat david, diana, douglas."""


class TestUnitestAction(unittest.TestCase):

    def setUp(self):
        self.famNs = Namespace('http://dev.w3.org/2000/10/swap/test/cwm/fam.n3#')
        self.nsMapping = dict(fam=self.famNs)
        # self.rules = HornFromN3('http://dev.w3.org/2000/10/swap/test/cwm/fam-rules.n3')
        self.rules = HornFromN3(StringIO(rules))
        # self.factGraph = Graph().parse(
        #     'http://dev.w3.org/2000/10/swap/test/cwm/fam.n3', format='n3')
        self.factGraph = Graph().parse(StringIO(facts), format='n3')
        self.factGraph.bind('fam', self.famNs)
        self.factGraph.bind('', self.famNs)
        dPreds = [self.famNs.ancestor]
        self.topDownStore = TopDownSPARQLEntailingStore(
            self.factGraph.store,
            self.factGraph,
            idb=self.rules,
            derivedPredicates=dPreds,
            nsBindings=self.nsMapping)

    def test_issue_008(self):
        # print(self.topDownStore.edb.serialize(format='n3').decode('utf-8'))
        targetGraph = Graph(store=self.topDownStore)
        targetGraph.bind('ex', self.famNs)
        # print(targetGraph.serialize(format="n3").decode('utf-8'))
        res = targetGraph.query(
            '''SELECT ?a { fam:david fam:ancestor ?a }''',
            initNs=self.nsMapping)
        # print("Len results: {}".format(len(list(res))))
        assert len(list(res)) is 0

if __name__ == '__main__':
    suite = unittest.makeSuite(TestUnitestAction)
    unittest.TextTestRunner(verbosity=5).run(suite)
